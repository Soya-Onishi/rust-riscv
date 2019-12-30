extern crate bitwise;

use super::status::Status;

use std::fmt;
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

    pub fn exec(&self, status: &mut Status) {
        match self.opcode {

        }
    }
}

fn make_panic_msg(name: EncodeType, field: &str) -> String {
    format!("{} does not have {} field", name, field)
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