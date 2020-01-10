extern crate bitwise;

use bitwise::*;
use bitwise::errors::Error;
use std::collections::HashMap;

pub struct Status {
    _pc: Bit,
    _regs: Vec<Bit>,
    _memory: HashMap<usize, [u8; 2048]>,
    _branch_delay_cycle: usize,
    _pc_queue: Vec<Option<Bit>>,
}

impl Status {
    pub fn get_pc(&self) -> Bit { self._pc.clone() }
    pub fn set_pc(&mut self, address: Bit) { self._pc = address }

    pub fn read_reg_value(&self, index: Bit) -> Result<Bit, Error> {
        let index = index.as_u8()? as usize;
        let value = match index {
            0 => Bit::new(0),
            i => self._regs[i].clone(),
        };

        Ok(value)
    }

    pub fn write_reg_value(&mut self, value: Bit, index: Bit) -> Result<(), Error>{
        let index = index.as_u8()? as usize;
        if index != 0 {
            self._regs[index] = value
        }

        Ok(())
    }

    pub fn read_mem_value(&self, address: &Bit) -> Result<Bit, Error> {
        let (offset, index) =
            separate_addr(address.as_u32()? as usize);

         match self._memory.get(&offset) {
            Some(&table) => Bit::new_with_length(table[index] as u32, 8),
            None => Bit::new_with_length(0, 8),
        }
    }

    pub fn write_mem_value(&mut self, value: Bit, address: &Bit) -> Result<(), Error> {
        let address = address.as_u32()? as usize;
        let (_, mut bytes) = value.value().to_bytes_le();
        let length = value.length() / 8;
        let mut pad =
            if bytes.len() < length {
                vec![0; length - bytes.len()]
            } else {
                vec![]
            };
        bytes.append(&mut pad);

        for (&byte, offset) in bytes.iter().zip(0..length) {
            let (offset, index) = separate_addr(address + offset);

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

        Ok(())
    }

    pub fn push_queue(&mut self, address: Bit) {
        let depth = self._branch_delay_cycle;
        self._pc_queue[depth - 1] = Some(address)
    }

    pub fn pop_queue(&mut self) -> Option<Bit> {
        let queue = self._pc_queue.clone();
        let (dest, remains) = queue.split_at(1);
        self._pc_queue = remains.to_vec();
        self._pc_queue.push(None);

        dest[0].clone()
    }
}

fn separate_addr(address: usize) -> (usize, usize) {
    let offset = address >> 11;
    let index = address & ((1 << 11) - 1);

    (offset as usize, index as usize)
}