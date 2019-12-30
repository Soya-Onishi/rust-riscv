extern crate bitwise;

use bitwise::Bit;
use std::collections::HashMap;

pub struct Status {
    regs: Vec<Bit>,
    memory: HashMap<u32, [Bit; 1024]>
}