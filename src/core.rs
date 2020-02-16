pub mod csr;
pub mod reg;
pub mod memory;
pub mod branch_manager;

use super::util::{
    instruction::Instruction,
    bitwise::Bitwise,
    exception::Exception,
};

use csr::*;
use reg::RegFile;
use memory::MMU;
use branch_manager::BranchManager;

pub struct Core {
    pub pc: u32,
    pub ireg: RegFile<u32>,
    pub csr: CSRFile,
    pub mmu: MMU,
    pub branch_manager: BranchManager,
    pub use_builtin_exception_handler: bool,
    pub is_turnon: bool,
}

impl Core {
    pub fn new(delay_cycle: usize, use_builtin_exception_handler: bool) -> Core {
        let ireg = RegFile::<u32>::new();
        let csr = CSRFile::new();
        let memory = MMU::new();
        let branch_manager = BranchManager::new(delay_cycle);

        Core {
            pc: 0,
            ireg,
            csr,
            mmu: memory,
            branch_manager,
            use_builtin_exception_handler,
            is_turnon: true,
        }
    }

    pub fn execute(&mut self) {
        match self.execute_one_instrunction() {
            Ok(()) => match self.branch_manager.pop_queue() {
                Some(addr) => self.pc = addr,
                None       => self.pc += 4
            }
            Err(exp) => self.raise_exception(exp),
        }        
    }

    fn execute_one_instrunction(&mut self) -> Result<(), Exception>{
        let inst = self.fetch()?;
        let inst = Instruction::new(inst)?;
        inst.exec(self)?;

        Ok(())
    }

    fn fetch(&self) -> Result<u32, Exception> {
        self.mmu.read_u32(self.pc)
    }

    fn raise_exception(&mut self, exp: Exception) {
        match exp {
            Exception::EnvironmentalCallMMode |
            Exception::EnvironmentalCallSMode |
            Exception::EnvironmentalCallUMode if self.use_builtin_exception_handler => {
                let a0 = self.ireg.read(10);

                match a0 {
                    1 => {
                        let a7 = self.ireg.read(17);
                        print!("{}", a7);
                    }
                    10 => self.is_turnon = false,
                    _ => {
                        println!("unknown ecall code: {}", a0);
                        self.is_turnon = false;
                    },
                }

                self.pc += 4;            
            }
            _ => {
                let trap_vector = self.csr.make_exception_vector(exp);
                let tval = exp.get_tval();
                let cause = exp.get_cause();

                let _ = self.csr.write(M_T_VAL, tval, 0);
                let _ = self.csr.write(M_CAUSE, cause, 0);
                let _ = self.csr.write(M_E_PC, self.pc, 0);
                self.csr.set_mpie(self.csr.get_mie() == 1);
                self.csr.set_mie(false);
                self.csr.set_mpp(0b11);

                self.branch_manager.flush_queue();
                self.pc = trap_vector;
            }
        }
    }
}