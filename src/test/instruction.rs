extern crate rand;
extern crate bitwise;

use rand::Rng;
use rand::rngs::ThreadRng;
use bitwise::*;
use super::super::util::{status::*, instruction::*};

fn construct_utype_inst(opcode_value: u32, &mut rng: ThreadRng) -> (Instruction, u32, u32){
    let imm: u32 = rng.gen() & 0b1111_1111_1111_1111_1111_0000_0000_0000;
    let rd: u32 = rng.gen_range(0, 31);
    let inst = Bit::new(imm | (rd << 7) | opcode_value);

    (Instruction::new(inst), imm, rd)
}

#[test]
fn construct_lui() {
    let rng = rand::thread_rng();
    let lui_op: u32 = 0b0110111;
    for _ in 0..100 {
        let (inst, imm, rd) = construct_utype_inst(lui_op, rng)
        assert_eq!(inst.rd(), Bit::new(rd));
        assert_eq!(inst.imm(), Bit::new(imm));
    }

}