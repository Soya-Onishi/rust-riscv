extern crate bitwise;

use bitwise::*;
use std::collections::HashMap;

pub struct Status {
    regs: Vec<Bit>,
    memory: HashMap<usize, [u8; 2048]>
}

impl Status {
    pub fn read_reg_value(&self, index: Bit) -> Bit {
        let index = index.as_u8() as usize;

        self.regs[index].clone()
    }

    pub fn write_reg_value(&mut self, value: Bit, index: Bit) {
        let index = index.as_u8() as usize;
        self.regs[index] = value;
    }

    pub fn read_mem_value(&self, address: Bit) -> Bit {
        let (offset, index) = separate_addr(address.as_u32());

        match self.memory.get(&offset) {
            Some(&table) => Bit::new((table[index] as u32, 8)),
            None => Bit::new((0, 8)),
        }
    }

    pub fn write_mem_value(&mut self, value: Bit, address: Bit) {
        let address = address.as_u32();
        let (_, bytes) = value.value().to_bytes_le();

        for (&byte, addr) in bytes.iter().zip(address..) {
            let (offset, index) = separate_addr(addr);

            match self.memory.get_mut(&offset) {
                Some(table) => {
                    table[index as usize] = byte;
                }
                None => {
                    let mut table = [0_u8; 2048];
                    table[index as usize] = byte;
                    self.memory.insert(offset, table);
                }
            }
        }
    }
}

fn separate_addr(address: u32) -> (usize, usize) {
    let offset = address >> 11;
    let index = address & ((1 << 11) - 1);

    (offset as usize, index as usize)
}