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
                    0b101 if funct7_bit == 0b010_0000 => Opcode::SRA,
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
                let bit0 = Bit::new_with_length(0, 1)?;
                Bit::concat(vec![&bit12, &bit11, &bit10_5, &bit4_1, &bit0])?.sign_ext(32)
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

#[derive(Clone, Copy, Debug, PartialEq)]
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
    extern crate bitwise;

    use super::{Instruction, Opcode};
    use rand::{Rng, SeedableRng, rngs::StdRng};

    use bitwise::*;

    fn bit_truncate(bit: u32, upper: u32, lower: u32) -> u32 {
        let mask = if (upper + 1) > 31 { 0 } else { 1_u32 << (upper + 1) };
        (bit & (mask.wrapping_sub(1) ^ 1_u32.wrapping_shl(lower).wrapping_sub(1))) >> lower
    }

    fn sign_ext(bit: u32, index: u32) -> u32 {
        if bit_truncate(bit, index, index) == 1 {
            bit | (0_u32.wrapping_sub(1) ^ 1_u32.wrapping_shl(index).wrapping_sub(1))
        } else {
            bit
        }
    }

    fn construct_utype_inst(opcode_value: u32, rng: &mut StdRng) -> (Instruction, u32, u32){
        let imm: u32 = rng.gen::<u32>() & 0b1111_1111_1111_1111_1111_0000_0000_0000;
        let rd: u32 = rng.gen_range(0, 31);
        let inst = Bit::new(imm | (rd << 7) | opcode_value);
        let inst = match Instruction::new(inst) {
            Ok(i) => i,
            Err(err) => panic!(err)
        };

        (inst, imm, rd)
    }

    fn construct_btype_inst(opcode: u32, funct3: u32, rng: &mut StdRng) -> (Instruction, Bit) {
        let imm: u32 = rng.gen::<u32>() & 0b1111_1110_0000_0000_0000_1111_1000_0000;
        let rs1: u32 = rng.gen_range(0, 31);
        let rs2: u32 = rng.gen_range(0, 31);

        let inst = Bit::new(imm | (rs1 << 15) | (rs2 << 20) | (funct3 << 12) | opcode);
        let inst = match Instruction::new(inst) {
            Ok(i) => i,
            Err(err) => panic!(err),
        };

        let imm = {
            println!("{:032b}", imm);

            let bit12 = bit_truncate(imm, 31, 31) << 12;
            let bit11 = bit_truncate(imm, 7, 7) << 11;
            let bit10_5 = bit_truncate(imm, 30, 25) << 5;
            let bit4_1 = bit_truncate(imm, 11, 8) << 1;

            sign_ext(bit12 | bit11 | bit10_5 | bit4_1, 12)
        };

        (inst, Bit::new(imm))
    }

    fn construct_jtype_inst(opcode: u32, rng: &mut StdRng) -> (Instruction, Bit, Bit) {
        let inst_imm = rng.gen::<u32>() & 0b1111_1111_1111_1111_1111_0000_0000_0000;
        let imm = {
            let bit20 = bit_truncate(inst_imm, 31, 31) << 20;
            let bit10_1 = bit_truncate(inst_imm, 30, 21) << 1;
            let bit11 = bit_truncate(inst_imm, 20, 20) << 11;
            let bit19_12 = bit_truncate(inst_imm, 19, 12) << 12;

            sign_ext((bit20 | bit19_12 | bit11 | bit10_1), 20)
        };
        let rd = rng.gen_range(0, 31);
        let inst = Bit::new(inst_imm | (rd << 7) | opcode);
        let inst = match Instruction::new(inst) {
            Ok(i) => i,
            Err(err) => panic!(err)
        };

        (inst, Bit::new(imm), Bit::new(rd))
    }

    fn construct_itype_inst(op: Opcode, opcode: u32, funct3: u32, rng: &mut StdRng) {
        let imm = rng.gen::<u32>() & 0b1111_1111_1111_0000_0000_0000_0000_0000;
        let rs1 = rng.gen_range(0, 31);
        let rd = rng.gen_range(0, 31);
        let inst = imm | (rs1 << 15) | (rd << 7) | (funct3 << 12) | opcode;
        let inst = Bit::new(inst);
        let inst = match Instruction::new(inst) {
            Ok(i) => i,
            Err(err) => panic!(err),
        };

        let imm = sign_ext(bit_truncate(imm, 31, 20), 11);

        assert_eq!(inst.opcode, op);
        assert_eq!(inst.imm().unwrap(), Bit::new(imm));
        assert_eq!(inst.rd().unwrap(), Bit::new(rd));
        assert_eq!(inst.rs1().unwrap(), Bit::new(rs1));
        assert_eq!(inst.funct3().unwrap(), Bit::new(funct3));
    }

    fn construct_itype_insts(op: Opcode, opcode: u32, funct3: u32) {
        let mut rng = SeedableRng::seed_from_u64(0);
        for _ in 0..100 {
            construct_itype_inst(op, opcode, funct3, &mut rng);
        }
    }

    fn construct_shift_inst(opcode: Opcode, funct3: u32, funct7: u32, rng: &mut StdRng) {
        let shamt = rng.gen_range(0, 31);
        let rs1 = rng.gen_range(0, 31);
        let rd = rng.gen_range(0, 31);
        let inst = (funct7 << 25) | (shamt << 20) | (rs1 << 15) | (funct3 << 12) | (rd << 7) | 0b0010011;
        let inst = match Instruction::new(Bit::new(inst)) {
            Ok(i) => i,
            Err(err) => panic!(err)
        };

        assert_eq!(inst.opcode, opcode);
        assert_eq!(inst.imm().unwrap(), Bit::new(shamt | (funct7 << 5)));
        assert_eq!(inst.rs1().unwrap(), Bit::new(rs1));
        assert_eq!(inst.rd().unwrap(), Bit::new(rd));
        assert_eq!(inst.funct3().unwrap(), Bit::new(funct3));
    }

    fn construct_shift_insts(opcode: Opcode, funct3: u32, funct7: u32) {
        let mut rng = SeedableRng::seed_from_u64(0);

        for _ in 0..100 {
            construct_shift_inst(opcode, funct3, funct7, &mut rng);
        }
    }

    fn construct_rtype_inst(op: Opcode, funct3: u32, funct7: u32, rng: &mut StdRng) {
        let rs1 = rng.gen_range(0, 31);
        let rs2 = rng.gen_range(0, 31);
        let rd = rng.gen_range(0, 31);
        let opcode = 0b0110011;
        let inst = (funct7 << 25) | (rs2 << 20) | (rs1 << 15) | (funct3 << 12) | (rd << 7) | opcode;
        let inst = match Instruction::new(Bit::new(inst)) {
            Ok(i) => i,
            Err(err) => panic!(err)
        };

        assert_eq!(inst.opcode, op);
        assert_eq!(inst.rs1().unwrap(), Bit::new(rs1));
        assert_eq!(inst.rs2().unwrap(), Bit::new(rs2));
        assert_eq!(inst.rd().unwrap(), Bit::new(rd));
        assert_eq!(inst.funct3().unwrap(), Bit::new(funct3));
        assert_eq!(inst.funct7().unwrap(), Bit::new(funct7));
    }

    fn construct_rtype_insts(opcode: Opcode, funct3: u32, funct7: u32) {
        let mut rng = SeedableRng::seed_from_u64(0);
        for _ in 0..100 {
            construct_rtype_inst(opcode, funct3, funct7, &mut rng);
        }
    }

    #[test]
    fn construct_lui() {
        let mut rng = SeedableRng::seed_from_u64(0);
        let lui_op: u32 = 0b0110111;
        for _ in 0..100 {
            let (inst, imm, rd) = construct_utype_inst(lui_op, &mut rng);
            assert_eq!(inst.rd().unwrap(), Bit::new(rd));
            assert_eq!(inst.imm().unwrap(), Bit::new(imm));
        }
    }

    #[test]
    fn construct_auipc() {
        let mut rng = SeedableRng::seed_from_u64(0);
        let auipc_op: u32 = 0b0010111;
        for _ in 0..100 {
            let (inst, imm, rd) = construct_utype_inst(auipc_op, &mut rng);
            assert_eq!(inst.opcode, Opcode::AUIPC);
            assert_eq!(inst.rd().unwrap(), Bit::new(rd));
            assert_eq!(inst.imm().unwrap(), Bit::new(imm));
        }
    }

    fn construct_branch(opcode: Opcode, funct3: u32) {
        let mut rng = SeedableRng::seed_from_u64(0);
        for _ in 0..100 {
            let (inst, imm) = construct_btype_inst(0b1100011, funct3, &mut rng);
            assert_eq!(inst.opcode, opcode);
            assert_eq!(inst.imm().unwrap(), imm);
        }
    }

    #[test]
    fn construct_beq() {
        construct_branch(Opcode::BEQ, 0b000);
    }

    #[test]
    fn construct_bne() {
        construct_branch(Opcode::BNE, 0b001);
    }

    #[test]
    fn construct_blt() {
        construct_branch(Opcode::BLT, 0b100);
    }

    #[test]
    fn construct_bge() {
        construct_branch(Opcode::BGE, 0b101);
    }

    #[test]
    fn construct_bltu() {
        construct_branch(Opcode::BLTU,0b110);
    }

    #[test]
    fn construct_bgeu() {
        construct_branch(Opcode::BGEU, 0b111);
    }

    #[test]
    fn construct_jal() {
        let mut rng = SeedableRng::seed_from_u64(0);
        for _ in 0..100 {
            let (inst, imm, rd) = construct_jtype_inst(0b1101111, &mut rng);
            assert_eq!(inst.opcode, Opcode::JAL);
            assert_eq!(inst.imm().unwrap(), imm);
            assert_eq!(inst.rd().unwrap(), rd);
        };
    }

    #[test]
    fn construct_jalr() {
        construct_itype_insts(Opcode::JALR, 0b1100111, 0b000);
    }

    #[test]
    fn construct_lb() {
        construct_itype_insts(Opcode::LB, 0b0000011, 0b000);
    }

    #[test]
    fn construct_lh() {
        construct_itype_insts(Opcode::LH, 0b0000011, 0b001);
    }

    #[test]
    fn construct_lw() {
        construct_itype_insts(Opcode::LW, 0b0000011, 0b010);
    }

    #[test]
    fn construct_lbu() {
        construct_itype_insts(Opcode::LBU, 0b0000011, 0b100);
    }

    #[test]
    fn construct_lhu() {
        construct_itype_insts(Opcode::LHU, 0b0000011, 0b101);
    }

    #[test]
    fn construct_addi() {
        construct_itype_insts(Opcode::ADDI, 0b0010011, 0b000);
    }

    #[test]
    fn construct_slti() {
        construct_itype_insts(Opcode::SLTI, 0b0010011, 0b010);
    }

    #[test]
    fn construct_sltiu() {
        construct_itype_insts(Opcode::SLTIU, 0b0010011, 0b011);
    }

    #[test]
    fn construct_xori() {
        construct_itype_insts(Opcode::XORI, 0b0010011, 0b100);
    }

    #[test]
    fn construct_ori() {
        construct_itype_insts(Opcode::ORI, 0b0010011, 0b110);
    }

    #[test]
    fn construct_andi() {
        construct_itype_insts(Opcode::ANDI, 0b0010011, 0b111);
    }

    #[test]
    fn construct_slli() {
        construct_shift_insts(Opcode::SLLI, 0b001, 0b000_0000);
    }

    #[test]
    fn construct_srli() {
        construct_shift_insts(Opcode::SRLI, 0b101, 0b000_0000);
    }

    #[test]
    fn construct_srai() {
        construct_shift_insts(Opcode::SRAI, 0b101, 0b010_0000);
    }

    #[test]
    fn construct_add() {
        construct_rtype_insts(Opcode::ADD, 0b000, 0b000_0000);
    }

    #[test]
    fn construct_sub() {
        construct_rtype_insts(Opcode::SUB, 0b000, 0b010_0000);
    }

    #[test]
    fn construct_sll() {
        construct_rtype_insts(Opcode::SLL, 0b001, 0b000_0000);
    }

    #[test]
    fn construct_slt() {
        construct_rtype_insts(Opcode::SLT, 0b010, 0b000_0000);
    }

    #[test]
    fn construct_sltu() {
        construct_rtype_insts(Opcode::SLTU, 0b011, 0b000_0000);
    }

    #[test]
    fn construct_xor() {
        construct_rtype_insts(Opcode::XOR, 0b100, 0b000_0000);
    }

    #[test]
    fn construct_srl() {
        construct_rtype_insts(Opcode::SRL, 0b101, 0b000_0000);
    }

    #[test]
    fn construct_sra() {
        construct_rtype_insts(Opcode::SRA, 0b101, 0b010_0000);
    }

    #[test]
    fn construct_or() {
        construct_rtype_insts(Opcode::OR, 0b110, 0b000_0000);
    }

    #[test]
    fn construct_and() {
        construct_rtype_insts(Opcode::AND, 0b111, 0b000_0000);
    }
}