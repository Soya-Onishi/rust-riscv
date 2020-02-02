pub struct BranchManager {
    delay_cycle: usize,
    delay_queue: Vec<Option<u32>>,
}

impl BranchManager {
    pub fn new(delay_cycle: usize) -> BranchManager {
        BranchManager {
            delay_cycle,
            delay_queue: vec![None; delay_cycle + 1],
        }
    }

    pub fn push_queue(&mut self, address: u32) {
        let depth = self.delay_cycle;
        self.delay_queue[depth] = Some(address)
    }

    pub fn pop_queue(&mut self) -> Option<u32> {
        let queue = self.delay_queue.clone();
        let (dest, remains) = queue.split_at(1);
        self.delay_queue = remains.to_vec();
        self.delay_queue.push(None);

        dest[0].clone()
    }

    pub fn flush_queue(&mut self) {
        self.delay_queue = vec![None; self.delay_cycle + 1];
    }
}