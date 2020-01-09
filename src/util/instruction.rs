extern crate bitwise;
extern crate num_bigint;

use super::status::Status;

use std::fmt;
use num_bigint::{Sign, BigInt};
use bitwise::*;
use bitwise::errors::Error;

pub struct Instruction {
    raw_code: Bit,
    opcode: Opcode,
    encode_type: EncodeType
}

impl Instruction {
    pub fn new(inst: Bit) -> Result<Instruction, Error> {
        let opcode_bit = inst.truncate((6, 0))?.as_u8()?;
        let funct3_bit = inst.truncate((14, 12))?.as_u8()?;
        let funct7_bit = inst.truncate((31, 25))?.as_u8()?;
        let funct12_bit = inst.truncate((31, 20))?.as_u32()?;

        let (opcode, encode_type) = match opcode_bit {
            0b0110111 => (Opcode::LUI, EncodeType::UType),
            0b0010111 => (Opcode::AUIPC, EncodeType::UType),
            0b1101111 => (Opcode::JAL, EncodeType::JType),
            0b1100111 if funct3_bit == 0b000 => (Opcode::JALR, EncodeType::IType),
            0b1100011 => {
                let opcode = match funct3_bit {
                    0b000 => Opcode::BEQ,
                    0b001 => Opcode::BNE,
                    0b100 => Opcode::BLT,
                    0b101 => Opcode::BGE,
                    0b110 => Opcode::BLTU,
                    0b111 => Opcode::BGEU,
                    _ => panic!("unexpected pattern match"),
                };

                (opcode, EncodeType::BType)
            }
            0b0000011 => {
                let opcode = match funct3_bit {
                    0b000 => Opcode::LB,
                    0b001 => Opcode::LH,
                    0b010 => Opcode::LW,
                    0b100 => Opcode::LBU,
                    0b101 => Opcode::LHU,
                    _ => panic!("unexpected pattern match"),
                };

                (opcode, EncodeType::IType)
            }
            0b0100011 => {
                let opcode = match funct3_bit {
                    0b000 => Opcode::SB,
                    0b001 => Opcode::SH,
                    0b010 => Opcode::SW,
                    _ => panic!("unexpected pattern match"),
                };

                (opcode, EncodeType::SType)
            }
            0b0010011 => {
                let opcode = match funct3_bit {
                    0b000 => Opcode::ADDI,
                    0b010 => Opcode::SLTI,
                    0b011 => Opcode::SLTIU,
                    0b100 => Opcode::XORI,
                    0b110 => Opcode::ORI,
                    0b111 => Opcode::ANDI,
                    0b001 if funct7_bit == 0b000_0000 => Opcode::SLLI,
                    0b101 if funct7_bit == 0b000_0000 => Opcode::SRLI,
                    0b101 if funct7_bit == 0b010_0000 => Opcode::SRAI,
                    _ => panic!("unexpected pattern match"),
                };

                (opcode, EncodeType::IType)
            }
            0b0110011 => {
                let opcode = match funct3_bit {
                    0b000 if funct7_bit == 0b000_0000 => Opcode::ADD,
                    0b000 if funct7_bit == 0b010_0000 => Opcode::SUB,
                    0b001 if funct7_bit == 0b000_0000 => Opcode::SLL,
                    0b010 if funct7_bit == 0b000_0000 => Opcode::SLT,
                    0b011 if funct7_bit == 0b000_0000 => Opcode::SLTU,
                    0b100 if funct7_bit == 0b000_0000 => Opcode::XOR,
                    0b101 if funct7_bit == 0b000_0000 => Opcode::SRL,
                    0b101 if funct7_bit == 0b000_0000 => Opcode::SRA,
                    0b110 if funct7_bit == 0b000_0000 => Opcode::OR,
                    0b111 if funct7_bit == 0b000_0000 => Opcode::AND,
                    _ => panic!("unexpected pattern match"),
                };

                (opcode, EncodeType::RType)
            }
            0b0001111 if funct3_bit == 0b000 => (Opcode::FENCE, EncodeType::IType),
            0b1110011 if funct12_bit == 0b0000_0000_0000 => (Opcode::ECALL, EncodeType::IType),
            0b1110011 if funct12_bit == 0b0000_0000_0001 => (Opcode::EBREAK, EncodeType::IType),
            _ => panic!("invalid instruction code"),
        };

        Ok(Instruction { raw_code: inst, opcode, encode_type })
    }

    fn rs1(&self) -> Result<Bit, Error> {
        match self.encode_type {
            EncodeType::RType |
            EncodeType::IType |
            EncodeType::SType |
            EncodeType::BType => self.raw_code.truncate((19, 15)),
            tpe => panic!(make_panic_msg(tpe, "rs1"))
        }
    }

    fn rs2(&self) -> Result<Bit, Error> {
        match self.encode_type {
            EncodeType::RType |
            EncodeType::SType |
            EncodeType::BType => self.raw_code.truncate((24, 20)),
            tpe => panic!(make_panic_msg(tpe, "rs2"))
        }
    }

    fn rd(&self) -> Result<Bit, Error> {
        match self.encode_type {
            EncodeType::RType |
            EncodeType::IType |
            EncodeType::UType |
            EncodeType::JType => self.raw_code.truncate((11, 7)),
            tpe => panic!(make_panic_msg(tpe, "rd"))
        }
    }

    fn imm(&self) -> Result<Bit, Error> {
        match self.encode_type {
            EncodeType::RType =>
                panic!(make_panic_msg(EncodeType::RType, "imm")),
            EncodeType::IType =>
                self.raw_code.truncate((31, 20))?.sign_ext(32),
            EncodeType::SType => {
                let upper = self.raw_code.truncate((31, 25))?;
                let lower = self.raw_code.truncate((11, 7))?;

                Bit::concat(vec![&upper, &lower])?.sign_ext(32)
            }
            EncodeType::BType => {
                let bit12 = self.raw_code.truncate(31)?;
                let bit11 = self.raw_code.truncate(7)?;
                let bit10_5 = self.raw_code.truncate((30, 25))?;
                let bit4_1 = self.raw_code.truncate((11, 8))?;

                Bit::concat(vec![&bit12, &bit11, &bit10_5, &bit4_1])?.sign_ext(32)
            }
            EncodeType::UType => {
                let bit31_12 = self.raw_code.truncate((31, 12))?;
                let bit11_0 = Bit::new_with_length(0, 12)?;

                Bit::concat(vec![&bit31_12, &bit11_0])
            }
            EncodeType::JType => {
                let bit20 = self.raw_code.truncate(31)?;
                let bit19_12 = self.raw_code.truncate((19, 12))?;
                let bit11 = self.raw_code.truncate(20)?;
                let bit10_1 = self.raw_code.truncate((30, 21))?;
                let bit0 = Bit::new_with_length(0, 1)?;

                let bit = Bit::concat(vec![&bit20, &bit19_12, &bit11, &bit10_1, &bit0])?;
                bit.sign_ext(32)
            }
        }
    }

    fn funct3(&self) -> Result<Bit, Error> {
        match self.encode_type {
            EncodeType::RType |
            EncodeType::IType |
            EncodeType::SType |
            EncodeType::BType => self.raw_code.truncate((14, 12)),
            tpe => panic!(make_panic_msg(tpe, "funct3")),
        }
    }

    fn funct7(&self) -> Result<Bit, Error> {
        match self.encode_type {
            EncodeType::RType => self.raw_code.truncate((31, 25)),
            tpe => panic!(make_panic_msg(tpe, "funct7")),
        }
    }

    fn lui(&self, status: &mut Status) -> Result<(), Error>{
        status.write_reg_value(
            self.imm()?,
            self.rd()?,
        )
    }

    fn auipc(&self, status: &mut Status) -> Result<(), Error> {
        status.write_reg_value(
            self.imm()? + status.get_pc(),
            self.rd()?,
        )
    }

    fn jal(&self, status: &mut Status) -> Result<(), Error> {
        let dest = self.imm()? + status.get_pc();
        let next_pc = status.get_pc() + Bit::new(4);

        status.push_queue(dest);
        status.write_reg_value(next_pc, self.rd()?)
    }

    fn jalr(&self, status: &mut Status) -> Result<(), Error> {
        let rs1_value = status.read_reg_value(self.rs1()?)?;
        let dest = self.imm()? + rs1_value + status.get_pc();
        let next_pc = status.get_pc() + Bit::new(4);

        status.push_queue(dest);
        status.write_reg_value(next_pc, self.rd()?);

        Ok(())
    }

    // execute branch instruction operation
    fn branch(&self, status: &mut Status, f: impl Fn(Bit, Bit) -> Result<bool, Error>) -> Result<(), Error>{
        let rs1_value = status.read_reg_value(self.rs1()?)?;
        let rs2_value = status.read_reg_value(self.rs2()?)?;

        let branch_dest =
            if f(rs1_value, rs2_value)? {
                status.get_pc() + self.imm()?
            } else {
                status.get_pc() + Bit::new(4)
            };

        status.push_queue(branch_dest);

        Ok(())
    }

    fn beq(&self, status: &mut Status) -> Result<(), Error> { self.branch(status, |a, b| Ok(a == b)) }
    fn bne(&self, status: &mut Status) -> Result<(), Error> { self.branch(status, |a, b| Ok(a != b)) }
    fn blt(&self, status: &mut Status) -> Result<(), Error> {
        self.branch(status, |a, b| {
            let a = convert_into_signed_value(&a)?;
            let b = convert_into_signed_value(&b)?;

            Ok(a < b)
        })
    }
    fn bge(&self, status: &mut Status) -> Result<(), Error> {
        self.branch(status, |a, b| {
            let a = convert_into_signed_value(&a)?;
            let b = convert_into_signed_value(&b)?;
            Ok(a >= b)
        })
    }
    fn bltu(&self, status: &mut Status) -> Result<(), Error> { self.branch(status, |a, b| Ok(a < b)) }
    fn bgeu(&self, status: &mut Status) -> Result<(), Error> { self.branch(status, |a, b| Ok(a >= b)) }

    fn load(&self, status: &mut Status, byte_count: u32, use_sign_ext: bool) -> Result<(), Error>{
        let base_addr = self.rs1()? + self.imm()?;
        let data = status.read_mem_value(&base_addr)?;
        let data = (1..byte_count).try_fold(data, |attached, offset| {
            let addr = base_addr.clone() + Bit::new(offset);
            let attach_data = status.read_mem_value(&addr)?;

            Bit::concat(vec![&attach_data, &attached])
        })?;

        let data =
            if use_sign_ext {
                data.sign_ext(32)?
            } else {
                data.zero_ext(32)?
            };

        status.write_reg_value(data, self.rd()?)
    }

    fn lb(&self, status: &mut Status) -> Result<(), Error> { self.load(status, 1, true) }
    fn lh(&self, status: &mut Status) -> Result<(), Error> { self.load(status, 2, true) }
    fn lw(&self, status: &mut Status) -> Result<(), Error> { self.load(status, 4, true) }
    fn lbu(&self, status: &mut Status) -> Result<(), Error> { self.load(status, 1, false) }
    fn lhu(&self, status: &mut Status) -> Result<(), Error> { self.load(status, 2, false) }

    fn store(&self, status: &mut Status, byte_size: usize) -> Result<(), Error> {
        let addr = self.rs1()? + self.imm()?;
        let data = status.read_reg_value(self.rs2()?)?;
        let data = data.truncate((byte_size * 8 - 1, 0))?;

        status.write_mem_value(data, &addr)
    }

    fn sb(&self, status: &mut Status) -> Result<(), Error> { self.store(status, 1) }
    fn sh(&self, status: &mut Status) -> Result<(), Error> { self.store(status, 2) }
    fn sw(&self, status: &mut Status) -> Result<(), Error> { self.store(status, 4) }

    fn rs1_imm_ops(&self, status: &mut Status, f: impl Fn(Bit, Bit) -> Result<Bit, Error>) -> Result<(), Error> {
        let rs1_value = status.read_reg_value(self.rs1()?)?;
        let imm_value = self.imm()?;
        let result = f(rs1_value, imm_value)?;

        status.write_reg_value(result, self.rd()?)
    }

    fn addi(&self, status: &mut Status)-> Result<(), Error> {
        self.rs1_imm_ops(status, |rs1, imm| Ok(rs1 + imm))
    }

    fn slti(&self, status: &mut Status) -> Result<(), Error> {
        self.rs1_imm_ops(status, |rs1, imm| {
            let converter = convert_into_signed_value;
            let value = if converter(&rs1)? < converter(&imm)? { Bit::new(1)} else { Bit::new(0) };

            Ok(value)
        })
    }

    fn sltiu(&self, status: &mut Status) -> Result<(), Error> {
        self.rs1_imm_ops(status, |rs1, imm| {
            let value = if rs1 < imm { Bit::new(1) } else { Bit::new(0) };

            Ok(value)
        })
    }

    fn xori(&self, status: &mut Status) -> Result<(), Error> {
        self.rs1_imm_ops(status, |rs1, imm| { Ok(rs1 ^ imm) } )
    }

    fn ori(&self, status: &mut Status) -> Result<(), Error> {
        self.rs1_imm_ops(status, |rs1, imm| { Ok(rs1 | imm) } )
    }

    fn andi(&self, status: &mut Status) -> Result<(), Error> {
        self.rs1_imm_ops(status, |rs1, imm| { Ok(rs1 & imm) } )
    }

    fn slli(&self, status: &mut Status) -> Result<(), Error> {
        self.rs1_imm_ops(status, |rs1, imm| {
            let shamt = imm.truncate((4, 0))?;
            let value = rs1 << shamt.as_u8()? as usize;

            Ok(value)
        })
    }

    fn srli(&self, status: &mut Status) -> Result<(), Error> {
        self.rs1_imm_ops(status, |rs1, imm| {
            let shamt = imm.truncate((4, 0))?.as_u8()? as usize;

            Ok(rs1 >> shamt)
        })
    }

    fn srai(&self, status: &mut Status) -> Result<(), Error> {
        self.rs1_imm_ops(
            status,
            |rs1, imm| arithmetic_right_shift(rs1, imm),
        )
    }

    fn rs1_rs2_ops(&self, status: &mut Status, f: impl Fn(Bit, Bit) -> Result<Bit, Error>) -> Result<(), Error> {
        let rs1_value = status.read_reg_value(self.rs1()?)?;
        let rs2_value = status.read_reg_value(self.rs2()?)?;
        let result = f(rs1_value, rs2_value)?;

        status.write_reg_value(result, self.rd()?)
    }

    fn add(&self, status: &mut Status) -> Result<(), Error> {
        self.rs1_rs2_ops(status, |rs1, rs2| Ok(rs1 + rs2))
    }

    fn sub(&self, status: &mut Status) -> Result<(), Error> {
        self.rs1_rs2_ops(status, |rs1, rs2| Ok(rs1 - rs2))
    }

    fn xor(&self, status: &mut Status) -> Result<(), Error> {
        self.rs1_rs2_ops(status, |rs1, rs2| Ok(rs1 ^ rs2))
    }

    fn or(&self, status: &mut Status) -> Result<(), Error> {
        self.rs1_rs2_ops(status, |rs1, rs2| Ok(rs1 | rs2))
    }

    fn and(&self, status: &mut Status) -> Result<(), Error> {
        self.rs1_rs2_ops(status, |rs1, rs2| Ok(rs1 & rs2))
    }

    fn slt(&self, status: &mut Status) -> Result<(), Error>{
        self.rs1_rs2_ops(status, |rs1, rs2| {
            let converter = convert_into_signed_value;
            let value = if converter(&rs1)? < converter(&rs2)? { Bit::new(1) } else { Bit::new(0) };
            Ok(value)
        })
    }

    fn sltu(&self, status: &mut Status) -> Result<(), Error> {
        self.rs1_rs2_ops(status, |rs1, rs2| {
            let value = if rs1 < rs2 { Bit::new(1) } else { Bit::new(0) };
            Ok(value)
        })
    }

    fn sll(&self, status: &mut Status) -> Result<(), Error>{
        self.rs1_rs2_ops(status, |rs1, rs2| {
            let shamt = rs2.as_u32()? as usize;

            Ok(rs1 << shamt)
        })
    }

    fn srl(&self, status: &mut Status) -> Result<(), Error> {
        self.rs1_rs2_ops(status, |rs1, rs2| {
            let shamt = rs2.as_u32()? as usize;

            Ok(rs1 >> shamt)
        })
    }

    fn sra(&self, status: &mut Status) -> Result<(), Error> {
        self.rs1_rs2_ops(
            status,
            |rs1, rs2| arithmetic_right_shift(rs1, rs2)
        )
    }

    // FENCE, ECALL and EBREAK instruction does not do anything
    fn fence(&self, status: &mut Status) -> Result<(), Error> { Ok(()) }
    fn ecall(&self, status: &mut Status) -> Result<(), Error> { Ok(()) }
    fn ebreak(&self, status: &mut Status) -> Result<(), Error> { Ok(()) }

    pub fn exec(&self, status: &mut Status) -> Result<(), Error> {
        match self.opcode {
            Opcode::LUI => self.lui(status),
            Opcode::AUIPC => self.auipc(status),
            Opcode::JAL => self.jal(status),
            Opcode::JALR => self.jalr(status),
            Opcode::BEQ => self.beq(status),
            Opcode::BNE => self.bne(status),
            Opcode::BLT => self.blt(status),
            Opcode::BGE => self.bge(status),
            Opcode::BLTU => self.bltu(status),
            Opcode::BGEU => self.bgeu(status),
            Opcode::LB => self.lb(status),
            Opcode::LH => self.lh(status),
            Opcode::LW => self.lw(status),
            Opcode::LBU => self.lbu(status),
            Opcode::LHU => self.lhu(status),
            Opcode::SB => self.sb(status),
            Opcode::SH => self.sh(status),
            Opcode::SW => self.sw(status),
            Opcode::ADDI => self.addi(status),
            Opcode::SLTI => self.slti(status),
            Opcode::SLTIU => self.sltiu(status),
            Opcode::XORI => self.xori(status),
            Opcode::ORI => self.ori(status),
            Opcode::ANDI => self.andi(status),
            Opcode::SLLI => self.slli(status),
            Opcode::SRLI => self.srli(status),
            Opcode::SRAI => self.srai(status),
            Opcode::ADD => self.add(status),
            Opcode::SUB => self.sub(status),
            Opcode::SLL => self.sll(status),
            Opcode::SLT => self.slt(status),
            Opcode::SLTU => self.sltu(status),
            Opcode::XOR => self.xor(status),
            Opcode::SRL => self.srl(status),
            Opcode::SRA => self.sra(status),
            Opcode::OR => self.or(status),
            Opcode::AND => self.and(status),
            Opcode::FENCE => self.fence(status),
            Opcode::ECALL => self.ecall(status),
            Opcode::EBREAK => self.ebreak(status),
        }
    }
}

fn make_panic_msg(name: EncodeType, field: &str) -> String {
    format!("{} does not have {} field", name, field)
}

fn convert_into_signed_value(value: &Bit) -> Result<BigInt, Error> {
    if value.truncate(31)? == Bit::new(1) {
        let value = -value.value();
        let (_, bytes) = value.to_bytes_be();

        Ok(BigInt::from_bytes_be(Sign::Minus, &bytes[..]))
    } else {
        Ok(value.value().clone())
    }
}

fn arithmetic_right_shift(value: Bit, shamt: Bit) -> Result<Bit, Error> {
    let shamt = shamt.truncate((4, 0))?.as_u8()? as usize;

    if value.truncate(31)? == Bit::new(1) && shamt > 0{
        let length = 32_usize - (1 << shamt);
        let mask = ((BigInt::new(Sign::Plus, vec![1]) << 32) - 1);
        let mask = mask << length;
        let mask: BigInt = mask & ((BigInt::new(Sign::Plus, vec![1]) << 32) - 1);
        let mask = Bit::new_with_length(mask.clone(), 32)?;

        Ok((value >> shamt) & mask)
    } else {
        Bit::new_with_length(value.value().clone(), 32)
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

#[cfg(test)]
mod test {
    use super::Instruction;
    use rand::Rng;
    use rand::rngs::ThreadRng;

    fn construct_utype_inst(opcode_value: u32, &mut rng: ThreadRng) -> (Instruction, u32, u32){
        let imm: u32 = rng.gen() & 0b1111_1111_1111_1111_1111_0000_0000_0000;
        let rd: u32 = rng.gen_range(0, 31);
        let inst = Bit::new(imm | (rd << 7) | opcode_value);
        let inst = match Instruction::new(inst) {
            Ok(i) => i,
            Err(err) => panic!(err)
        };

        (inst, imm, rd)
    }

    #[test]
    fn construct_lui() {
        let rng = rand::thread_rng();
        let lui_op: u32 = 0b0110111;
        for _ in 0..100 {
            let (inst, imm, rd) = construct_utype_inst(lui_op, rng);
            assert_eq!(inst.rd(), Bit::new(rd));
            assert_eq!(inst.imm(), Bit::new(imm));
        }
    }
}