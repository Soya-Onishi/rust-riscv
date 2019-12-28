extern crate bitwise;

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
            RType | IType | SType | BType=> {
                self.raw_code.truncate((19, 15))
            }
            tpe => panic!(make_panic_msg(tpe, "rs1"))
        }
    }


    fn rs2(&self) -> Bit {
        match self.encode_type {
            RType | SType | BType => {
                self.raw_code.truncate((24, 20))
            }
            tpe => panic!(make_panic_msg(tpe, "rs2"))
        }
    }

    fn rd(&self) -> Bit {
        match self.encode_type {
            RType | IType | UType | JType => {
                self.raw_code.truncate((11, 7))
            }
            tpe => panic!(make_panic_msg(tpe, "rd"))
        }
    }

    fn imm(&self) -> Bit {
        match self.encode_type {
            RType => panic!(make_panic_msg(RType, "imm")),
            IType => self.raw_code.truncate(31, 20),
            SType => {
                let upper = self.raw_code.truncate((31, 25));
                let lower = self.raw_code.truncate((11, 7));

                upper.concat(&lower)
            }
            BType => {
                let bit12 = self.raw_code.truncate(31);
                let bit11 = self.raw_code.truncate(7);
                let bit10_5 = self.raw_code.truncate((30, 25));
                let bit4_1 = self.raw_code.truncate((11, 8));

            }
            UType => {
                let bit31_12 = self.raw_code.truncate((31, 12));
            }
            JType => {
                let bit20 = self.raw_code.truncate(31);
                let bit19_12 = self.raw_code.truncate((19, 12));
                let bit11 = self.raw_code.truncate(20);
                let bit10_1 = self.raw_code.truncate((30, 21));
            }
        }
    }

    fn funct3(&self) -> Bit {
        match self.encode_type {
            RType | IType | SType | BType => {
                self.raw_code.truncate((14, 12))
            }
            tpe => panic!(make_panic_msg(tpe, "funct3")),
        }
    }

    fn funct7(&self) -> Bit {
        match self.encode_type {
            RType => self.raw_code.truncate((31, 25)),
            tpe => panic!(make_panic_msg(tpe, "funct7")),
        }
    }
}

fn make_panic_msg(name: EncodeType, field: &str) -> String {
    format!("{} does not have {} field", name, field)
}

#[derive(Clone, Copy, Debug, Display)]
enum EncodeType {
    RType,
    IType,
    SType,
    BType,
    UType,
    JType,
}

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