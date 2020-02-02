use std::collections::HashMap;

pub struct Memory {
    mem: HashMap<usize, [u8; 2048]>,
}

impl Memory {
    pub fn new() -> Memory {
        Memory { mem: HashMap::new() }
    }

    pub fn read(&self, address: u32) -> u8 {
        let (offset, index) = separate_addr(address);

        match self.mem.get(&offset) {
            Some(table) => table[index],
            None => 0
        }
    }

    pub fn write(&mut self, address: u32, value: u8) {
        let (offset, index) = separate_addr(address);
        match self.mem.get_mut(&offset) {
            Some(table) => table[index] = value,
            None => {
                let mut table = [0_u8; 2048];
                table[index] = value;
                self.mem.insert(offset, table);
            }
        }
    }
}

fn separate_addr(address: u32) -> (usize, usize) {
    let offset = address >> 11;
    let index = address & ((1 << 11) - 1);

    (offset as usize, index as usize)
}