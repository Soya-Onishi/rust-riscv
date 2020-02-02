pub mod csr;
pub mod reg;
pub mod memory;
pub mod branch_manager;
extern crate elf;

use std::fs;
use std::io;
use super::util::{
    instruction::Instruction,
    bitwise::Bitwise,
    exception::Exception,
};

use csr::*;
use reg::RegFile;
use memory::Memory;
use branch_manager::BranchManager;

pub struct Core {
    pub pc: u32,
    pub ireg: RegFile<u32>,
    pub csr: CSRFile,
    pub memory: Memory,
    pub branch_manager: BranchManager,
    pub use_builtin_ecall: bool,
    pub is_turnon: bool,
}

impl Core {
    pub fn new(delay_cycle: usize, use_builtin_ecall: bool) -> Core {
        let ireg = RegFile::<u32>::new();
        let csr = CSRFile::new();
        let memory = Memory::new();
        let branch_manager = BranchManager::new(delay_cycle);

        Core {
            pc: 0,
            ireg,
            csr,
            memory,
            branch_manager,
            use_builtin_ecall,
            is_turnon: true,
        }
    }

    pub fn load_and_run(&mut self, filename: String) {
        self.load(filename);
        self.execute();
    }

    fn load(&mut self, filename: String) {
        let binary = fs::read(filename).unwrap();
        let mut cursor = io::Cursor::new(binary);
        let elf = elf::File::open_stream(&mut cursor).unwrap();
        let sections = elf.sections;
        for section in sections.iter() {
            if section.shdr.shtype == elf::types::SHT_PROGBITS {
                let offset = section.shdr.offset as u32;
                let size = section.shdr.size as u32;
                let target_addr = section.shdr.addr as u32;
                let data = &section.data;

                for (&bin, index) in data.iter().zip(0..) {
                    self.memory.write(target_addr + index, bin)
                }
            }
        }

        self.pc = elf.ehdr.entry as u32;
    }

    fn run(&mut self) {
        while self.is_turnon {
            match self.execute() {
                Ok(()) => match self.branch_manager.pop_queue() {
                    Some(addr) => self.pc = addr,
                    None             => self.pc += 4
                }
                Err(exp) => self.raise_exception(exp),
            }
        }
    }

    fn execute(&mut self) -> Result<(), Exception>{
        let inst = self.fetch()?;
        let inst = Instruction::new(inst)?;
        inst.exec(self)?;

        Ok(())
    }

    fn fetch(&mut self) -> Result<u32, Exception> {
        let bytes = (0..4).map(|i| self.pc + i)
            .map(|addr| self.memory.read(addr) as u32)
            .collect::<Vec<u32>>();

        Ok(Bitwise::concat(&bytes, &[8; 4]))
    }

    fn raise_exception(&mut self, exp: Exception) {
        match exp {
            Exception::EnvironmentalCallMMode |
            Exception::EnvironmentalCallSMode |
            Exception::EnvironmentalCallUMode if self.use_builtin_ecall => self.run_built_in_ecall(),
            _ => {
                let trap_vector = self.csr.make_exception_vector(exp);
                let tval = exp.get_tval();
                let cause = exp.get_cause();

                self.csr.write(M_T_VAL, tval, 0);
                self.csr.write(M_CAUSE, cause, 0);
                self.csr.write(M_E_PC, self.pc, 0);
                self.csr.set_mpie(self.csr.get_mie() == 1);
                self.csr.set_mie(false);
                self.csr.set_mpp(0b11);

                self.branch_manager.flush_queue();
                self.pc = trap_vector;

            }
        }
    }

    fn run_built_in_ecall(&mut self) {
        let a0 = self.ireg.read(10);

        match a0 {
            0 => {
                let a7 = self.ireg.read(17);
                print!("{}", a7);
            }
            10 => self.is_turnon = false,
             _ => panic!("unknown ecall code: {}", a0),
        }
    }
}