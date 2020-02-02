pub struct RegFile<T>
    where T: Copy
{
    default: T,
    regs: [T; 32],
}

impl<T> RegFile<T>
    where T: Copy
{
    pub fn read(&self, addr: usize) -> T {
        if addr == 0 { self.default.clone() }
        else { self.regs[addr].clone() }
    }

    pub fn write(&mut self, addr: usize, value: T) {
        if addr != 0 { self.regs[addr] = value }
    }
}

impl RegFile<u32> {
    pub fn new() -> RegFile<u32> {
        RegFile {
            default: 0,
            regs: [0; 32],
        }
    }
}

impl RegFile<f32> {
    pub fn new() -> RegFile<f32> {
        RegFile {
            default: 0.0,
            regs: [0.0; 32],
        }
    }
}