extern crate bitwise;
extern crate num_bigint;

use super::status::Status;

use std::fmt;
use num_bigint::{Sign, BigInt};
use bitwise::*;

pub struct Instruction {
    raw_code: Bit,
    opcode: Opcode,
    encode_type: EncodeType
}

impl Instruction {
    fn rs1(&self) -> Bit {
        match self.encode_type {
            EncodeType::RType |
            EncodeType::IType |
            EncodeType::SType |
            EncodeType::BType => self.raw_code.truncate((19, 15)),
            tpe => panic!(make_panic_msg(tpe, "rs1"))
        }
    }

    fn rs2(&self) -> Bit {
        match self.encode_type {
            EncodeType::RType |
            EncodeType::SType |
            EncodeType::BType => self.raw_code.truncate((24, 20)),
            tpe => panic!(make_panic_msg(tpe, "rs2"))
        }
    }

    fn rd(&self) -> Bit {
        match self.encode_type {
            EncodeType::RType |
            EncodeType::IType |
            EncodeType::UType |
            EncodeType::JType => self.raw_code.truncate((11, 7)),
            tpe => panic!(make_panic_msg(tpe, "rd"))
        }
    }

    fn imm(&self) -> Bit {
        match self.encode_type {
            EncodeType::RType =>
                panic!(make_panic_msg(EncodeType::RType, "imm")),
            EncodeType::IType =>
                self.raw_code.truncate((31, 20)).sign_ext(32),
            EncodeType::SType => {
                let upper = self.raw_code.truncate((31, 25));
                let lower = self.raw_code.truncate((11, 7));

                Bit::concat(vec![&upper, &lower]).sign_ext(32)
            }
            EncodeType::BType => {
                let bit12 = self.raw_code.truncate(31);
                let bit11 = self.raw_code.truncate(7);
                let bit10_5 = self.raw_code.truncate((30, 25));
                let bit4_1 = self.raw_code.truncate((11, 8));

                Bit::concat(vec![&bit12, &bit11, &bit10_5, &bit4_1]).sign_ext(32)
            }
            EncodeType::UType => {
                let bit31_12 = self.raw_code.truncate((31, 12));

                Bit::concat(vec![&bit31_12, &Bit::new((0, 12))])
            }
            EncodeType::JType => {
                let bit20 = self.raw_code.truncate(31);
                let bit19_12 = self.raw_code.truncate((19, 12));
                let bit11 = self.raw_code.truncate(20);
                let bit10_1 = self.raw_code.truncate((30, 21));
                let bit0 = Bit::new((0, 1));

                let bit = Bit::concat(vec![&bit20, &bit19_12, &bit11, &bit10_1, &bit0]);
                bit.sign_ext(32)
            }
        }
    }

    fn funct3(&self) -> Bit {
        match self.encode_type {
            EncodeType::RType |
            EncodeType::IType |
            EncodeType::SType |
            EncodeType::BType => self.raw_code.truncate((14, 12)),
            tpe => panic!(make_panic_msg(tpe, "funct3")),
        }
    }

    fn funct7(&self) -> Bit {
        match self.encode_type {
            EncodeType::RType => self.raw_code.truncate((31, 25)),
            tpe => panic!(make_panic_msg(tpe, "funct7")),
        }
    }

    fn lui(&self, status: &mut Status) {
        status.write_reg_value(
            self.imm(),
            self.rd(),
        )
    }

    fn auipc(&self, status: &mut Status) {
        status.write_reg_value(
            self.imm() + status.get_pc(),
            self.rd(),
        )
    }

    fn jal(&self, status: &mut Status) {
        let dest = self.imm() + status.get_pc();
        let next_pc = status.get_pc() + Bit::new(4);

        status.push_queue(dest);
        status.write_reg_value(next_pc, self.rd());
    }

    fn jalr(&self, status: &mut Status) {
        let rs1_value = status.read_reg_value(self.rs1());
        let dest = self.imm() + rs1_value + status.get_pc();
        let next_pc = status.get_pc() + Bit::new(4);

        status.push_queue(dest);
        status.write_reg_value(next_pc, self.rd());
    }

    // execute branch instruction operation
    fn branch(&self, status: &mut Status, f: impl Fn(Bit, Bit) -> bool) {
        let rs1_value = status.read_reg_value(self.rs1());
        let rs2_value = status.read_reg_value(self.rs2());

        let branch_dest =
            if f(rs1_value, rs2_value){
                status.get_pc() + self.imm()
            } else {
                status.get_pc() + Bit::new(4)
            };

        status.push_queue(branch_dest);
    }

    fn beq(&self, status: &mut Status) { self.branch(status, |a, b| a == b); }
    fn bne(&self, status: &mut Status) { self.branch(status, |a, b| a != b); }
    fn blt(&self, status: &mut Status) {
        self.branch(status, |a, b| {
            let a = convert_into_signed_value(&a);
            let b = convert_into_signed_value(&b);
            a < b
        });
    }
    fn bge(&self, status: &mut Status) {
        self.branch(status, |a, b| {
            let a = convert_into_signed_value(&a);
            let b = convert_into_signed_value(&b);
            a >= b
        });
    }
    fn bltu(&self, status: &mut Status) { self.branch(status, |a, b| a < b); }
    fn bgeu(&self, status: &mut Status) { self.branch(status, |a, b| a >= b); }
    pub fn exec(&self, status: &mut Status) {
        match self.opcode {
            Opcode::LUI => self.lui(status),
            _ => (),
        }
    }
}

fn make_panic_msg(name: EncodeType, field: &str) -> String {
    format!("{} does not have {} field", name, field)
}

fn convert_into_signed_value(value: &Bit) -> BigInt {
    if value.truncate(31) == Bit::new(1) {
        let value = -value.value();
        let (_, bytes) = value.to_bytes_be();
        BigInt::from_bytes_be(Sign::Minus, &bytes[..])
    } else {
        value.value().clone()
    }
}

#[derive(Clone, Copy, Debug)]
enum EncodeType {
    RType,
    IType,
    SType,
    BType,
    UType,
    JType,
}

impl std::fmt::Display for EncodeType {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "{:?}", self)
    }
}

#[derive(Clone, Copy, Debug)]
enum Opcode {
    LUI,
    AUIPC,
    JAL,
    JALR,
    BEQ,
    BNE,
    BLT,
    BGE,
    BLTU,
    BGEU,
    LB,
    LH,
    LW,
    LBU,
    LHU,
    SB,
    SH,
    SW,
    ADDI,
    SLTI,
    SLTIU,
    XORI,
    ORI,
    ANDI,
    SLLI,
    SRLI,
    SRAI,
    ADD,
    SUB,
    SLL,
    SLT,
    SLTU,
    XOR,
    SRL,
    SRA,
    OR,
    AND,
    FENCE,
    ECALL,
    EBREAK,
}