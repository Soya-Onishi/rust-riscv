use std::collections::HashMap;

pub struct Status {
    pub pc: u32,
    iregs: [u32; 32],
    memory: HashMap<usize, [u8; 2048]>,
    branch_delay_cycle: usize,
    pc_queue: Vec<Option<u32>>,
    terminate: bool,
}

impl Status {
    pub fn new(delay_cycle: usize) -> Status {
        Status {
            pc: 0,
            pc_queue: vec![None; delay_cycle + 1],
            memory: HashMap::new(),
            iregs: [0; 32],
            branch_delay_cycle: delay_cycle,
            terminate: false,
        }
    }

    pub fn terminate_cpu(&mut self) { self.terminate = true; }
    pub fn is_terminate(&self) -> bool { self.terminate }

    pub fn read_reg_value(&self, index: usize) -> u32 {
        self.iregs[index]
    }

    pub fn write_reg_value(&mut self, value: u32, index: usize) {
        if index != 0 {
            self.iregs[index] = value;
        }
    }

    pub fn read_mem_value(&self, address: u32) -> u8 {
        let (offset, index) = separate_addr(address);

         match self.memory.get(&offset) {
            Some(table) => table[index],
            None => 0
        }
    }

    pub fn write_mem_value(&mut self, value: u8, address: u32) {
        let (offset, index) = separate_addr(address);
        match self.memory.get_mut(&offset) {
            Some(table) => table[index] = value,
            None => {
                let mut table = [0_u8; 2048];
                table[index] = value;
                self.memory.insert(offset, table);
            }
        }
    }

    pub fn push_queue(&mut self, address: u32) {
        let depth = self.branch_delay_cycle;
        self.pc_queue[depth] = Some(address)
    }

    pub fn pop_queue(&mut self) -> Option<u32> {
        let queue = self.pc_queue.clone();
        let (dest, remains) = queue.split_at(1);
        self.pc_queue = remains.to_vec();
        self.pc_queue.push(None);

        dest[0].clone()
    }

    pub fn dump_memory(&self) {
        let mut sorted_keys = self.memory.keys().collect::<Vec<&usize>>();
        sorted_keys.sort();

        for &offset in sorted_keys.iter() {
            let page = self.memory.get(offset).unwrap();

            for index in (0..2048).step_by(16) {
                if page[index..index + 16].iter().any(|&bin| bin != 0) {
                    print!("{:08x}: ", (offset << 11) + index);
                    for i in (index..index + 16) {
                        print!("{:02x} ", page[i]);
                        if i % 16 == 7 { print!(" ") }
                    }
                    println!();
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

#[cfg(test)]
mod test {
    extern crate bitwise;
    extern crate rand;

    use super::Status;
    use std::collections::HashMap;
    use bitwise::*;
    use rand::{Rng, SeedableRng};
    use rand::rngs::StdRng;

    #[test]
    fn read_write_registers() {
        let mut rng: StdRng = SeedableRng::seed_from_u64(0);
        let mut status = Status::new(0);

        for _ in 0..1000 {
            let index = rng.gen_range(0, 31);
            let value = rng.gen::<u64>();

            status.write_reg_value(value, index);

            let v = status.read_reg_value(index);

            if index == 0 { assert_eq!(v, 0); }
            else          { assert_eq!(v, value); }
        }
    }
}