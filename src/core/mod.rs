pub mod decoder;
pub mod csr;

extern crate elf;

use super::util::status::Status;
use std::fs;
use std::io;
use super::util::instruction::Instruction;
use super::util::bitwise::Bitwise;
use super::util::exception::Exception;
use csr::*;

pub struct Core {
    turnon: bool,
    status: Status
}

impl Core {
    pub fn new(delay_cycle: usize) -> Core {
        let status = Status::new(delay_cycle);

        Core {
            turnon: true,
            status,
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
                    self.status.write_mem(bin, target_addr + index)
                }
            }
        }

        self.status.pc = elf.ehdr.entry as u32;
    }

    fn run(&mut self) {
        while self.turnon {
            match self.execute() {
                Ok(()) => match self.status.pop_queue() {
                    Some(addr) => self.status.pc = addr,
                    None => self.status.pc += 4
                }
                Err(exp) => self.raise_exception(exp),
            }
        }
    }

    fn execute(&mut self) -> Result<(), Exception>{
        let inst = self.fetch()?;
        let inst = Instruction::new(inst)?;
        inst.exec(&mut self.status)?;

        match self.status.pop_queue() {
            Some(addr) => self.status.pc = addr,
            None => self.status.pc += 4,
        };

        Ok(())
    }

    fn fetch(&mut self) -> Result<u32, Exception> {
        let bytes = (0..4).map(|i| self.status.pc + i)
            .map(|addr| self.status.read_mem(addr) as u32)
            .collect::<Vec<u32>>();

        Ok(Bitwise::concat(&bytes, &[8; 4]))
    }

    fn raise_exception(&mut self, exp: Exception) {
        match exp {
            Exception::EnvironmentalCallMMode |
            Exception::EnvironmentalCallSMode |
            Exception::EnvironmentalCallUMode if self.status.built_in_ecall => self.run_built_in_ecall(),
            _ => {
                let trap_vector = self.status.csr.make_exception_vector(exp);
                let tval = exp.get_tval();
                let cause = exp.get_cause();

                self.status.csr.write(M_T_VAL, tval, 0);
                self.status.csr.write(M_CAUSE, cause, 0);
                self.status.csr.write(M_E_PC, self.status.pc, 0);
                self.status.csr.set_mpie(self.status.csr.get_mie() == 1);
                self.status.csr.set_mie(false);
                self.status.csr.set_mpp(0b11);

                self.status.flush_queue();
                self.status.pc = trap_vector;

            }
        }
    }

    fn run_built_in_ecall(&mut self) {
        let a0 = self.status.read_reg(10);

        match a0 {
            0 => {
                let a7 = self.status.read_reg(17);
                print!("{}", a7);
            }
            10 => self.turnon = false,
             _ => panic!("unknown ecall code: {}", a0),
        }
    }
}