extern crate bitwise;

use bitwise::*;
use std::collections::HashMap;

pub struct Status {
    _pc: Bit,
    _regs: Vec<Bit>,
    _memory: HashMap<usize, [u8; 2048]>,
    _pc_queue_depth: usize,
    _pc_queue: Vec<Option<Bit>>,
}

impl Status {
    pub fn get_pc(&self) -> Bit { self._pc.clone() }
    pub fn set_pc(&mut self, address: Bit) { self._pc = address }

    pub fn read_reg_value(&self, index: Bit) -> Bit {
        let index = index.as_u8() as usize;

        self._regs[index].clone()
    }

    pub fn write_reg_value(&mut self, value: Bit, index: Bit) {
        let index = index.as_u8() as usize;
        self._regs[index] = value;
    }

    pub fn read_mem_value(&self, address: Bit) -> Bit {
        let (offset, index) = separate_addr(address.as_u32());

        match self._memory.get(&offset) {
            Some(&table) => Bit::new((table[index] as u32, 8)),
            None => Bit::new((0, 8)),
        }
    }

    pub fn write_mem_value(&mut self, value: Bit, address: Bit) {
        let address = address.as_u32();
        let (_, bytes) = value.value().to_bytes_le();

        for (&byte, addr) in bytes.iter().zip(address..) {
            let (offset, index) = separate_addr(addr);

            match self._memory.get_mut(&offset) {
                Some(table) => {
                    table[index as usize] = byte;
                }
                None => {
                    let mut table = [0_u8; 2048];
                    table[index as usize] = byte;
                    self._memory.insert(offset, table);
                }
            }
        }
    }

    fn push_queue(&mut self, address: Bit) {
        let depth = self._pc_queue_depth;
        self._pc_queue[depth - 1] = Some(address)
    }

    fn pop_queue(&mut self, address: Bit) -> Option<Bit> {
        let dest = self._pc_queue[0];
        let remains = self._pc_queue[1..];
        self._pc_queue = remains.to_vec();
        self._pc_queue.push(None);

        dest
    }
}

fn separate_addr(address: u32) -> (usize, usize) {
    let offset = address >> 11;
    let index = address & ((1 << 11) - 1);

    (offset as usize, index as usize)
}