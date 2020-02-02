mod decoder;
mod csr;

extern crate elf;

use super::util::status::Status;
use std::fs;
use std::io;
use super::util::instruction::Instruction;
use super::util::bitwise::Bitwise;

pub struct Core {
    status: Status
}

impl Core {
    pub fn new(delay_cycle: usize) -> Core {
        let status = Status::new(delay_cycle);

        Core { status }
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

    fn execute(&mut self) {
        loop {
            let inst = self.fetch();

            let inst = Instruction::new(inst);
            inst.exec(&mut self.status);

            match self.status.pop_queue() {
                Some(addr) => self.status.pc = addr,
                None => self.status.pc += 4,
            };

            if self.status.is_terminate() { break }
        }
    }

    fn fetch(&mut self) -> u32 {
        let bytes = (0..4).map(|i| self.status.pc + i)
            .map(|addr| self.status.read_mem(addr) as u32)
            .collect::<Vec<u32>>();

        Bitwise::concat(&bytes, &[8; 4])
    }
}