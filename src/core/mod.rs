mod decoder;

extern crate bitwise;
extern crate elf_reader;

use super::util::status::Status;
use std::fs;
use std::io;
use bitwise::*;
use crate::util::instruction::Instruction;

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

        let elf = elf_reader::ELF::<u32>::new(binary).unwrap();
        let sections = elf.section_headers();
        let data = elf.data();
        for section in sections.iter() {
            if section.section_type() == elf_reader::SectionType::ProgBits {
                let offset = section.file_offset() as usize;
                let size = section.size() as usize;
                let target_addr = section.target_addr() as usize;

                for (&bin, index) in data[offset..offset + size].iter().zip(0..) {
                    self.status.write_mem_value_directly(bin, target_addr + index)
                }
            }
        }

        self.status.set_pc(Bit::new(elf.header().entry_point()));
    }

    fn execute(&mut self) {
        loop {
            let inst = self.fetch().unwrap();
            println!("execute: {:08x}", inst.value());

            let inst = Instruction::new(inst).unwrap();
            inst.exec(&mut self.status).unwrap();

            match self.status.pop_queue() {
                Some(addr) => self.status.set_pc(addr),
                None => self.status.set_pc(self.status.get_pc() + Bit::new(4)),
            };
        }
    }

    pub fn start(&mut self, pc: Bit) {
        self.status.set_pc(pc);
    }

    fn fetch(&mut self) -> Result<Bit, errors::Error>{
        let pc = self.status.get_pc();
        let addrs = (0..4).map(|i| pc.clone() + Bit::new(i)).rev().collect::<Vec<Bit>>();
        let bytes = addrs.iter()
            .map(|addr| self.status.read_mem_value(addr))
            .collect::<Result<Vec<Bit>, errors::Error>>()?;

        let bytes = bytes.iter().collect();

        Bit::concat(bytes)
    }
}