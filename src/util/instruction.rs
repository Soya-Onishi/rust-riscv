extern crate num_bigint;

use std::fmt;
use super::bitwise::Bitwise;
use super::exception::Exception;
use super::super::core::Core;
use crate::core::csr::M_E_PC;

pub struct Instruction {
    raw_code: u32,
    opcode: Opcode,
    encode_type: EncodeType
}

impl Instruction {
    /*
    pub fn new(inst: u32) -> Result<Instruction, Exception> {
        let opcode = inst.truncate(6, 0);
        let funct3 = inst.truncate(14, 12);
        let funct7 = inst.truncate(31, 25);
        let funct12 = inst.truncate(31, 20);

        let (opcode, encode_type) = match opcode {
            0b0110111 => (Opcode::LUI, EncodeType::UType),
            0b0010111 => (Opcode::AUIPC, EncodeType::UType),
            0b1101111 => (Opcode::JAL, EncodeType::JType),
            0b1100111 => match funct3 {
                0b000 => (Opcode::JALR, EncodeType::IType),
                _     => Err(Exception::IllegalInstruction(inst))?,
            },
            0b1100011 => {
                let opcode = match funct3 {
                    0b000 => Opcode::BEQ,
                    0b001 => Opcode::BNE,
                    0b100 => Opcode::BLT,
                    0b101 => Opcode::BGE,
                    0b110 => Opcode::BLTU,
                    0b111 => Opcode::BGEU,
                    _     => Err(Exception::IllegalInstruction(inst))?,
                };

                (opcode, EncodeType::BType)
            }
            0b0000011 => {
                let opcode = match funct3 {
                    0b000 => Opcode::LB,
                    0b001 => Opcode::LH,
                    0b010 => Opcode::LW,
                    0b100 => Opcode::LBU,
                    0b101 => Opcode::LHU,
                        _ => Err(Exception::IllegalInstruction(inst))?,
                };

                (opcode, EncodeType::IType)
            }
            0b0100011 => {
                let opcode = match funct3 {
                    0b000 => Opcode::SB,
                    0b001 => Opcode::SH,
                    0b010 => Opcode::SW,
                        _ => Err(Exception::IllegalInstruction(inst))?,
                };

                (opcode, EncodeType::SType)
            }
            0b0010011 => {
                let opcode = match funct3 {
                    0b000 => Opcode::ADDI,
                    0b010 => Opcode::SLTI,
                    0b011 => Opcode::SLTIU,
                    0b100 => Opcode::XORI,
                    0b110 => Opcode::ORI,
                    0b111 => Opcode::ANDI,
                    0b001 if funct7 == 0b000_0000 => Opcode::SLLI,
                    0b101 if funct7 == 0b000_0000 => Opcode::SRLI,
                    0b101 if funct7 == 0b010_0000 => Opcode::SRAI,
                        _ => Err(Exception::IllegalInstruction(inst))?,
                };

                (opcode, EncodeType::IType)
            }
            0b0110011 => {
                let opcode = match funct3 {
                    0b000 if funct7 == 0b000_0000 => Opcode::ADD,
                    0b000 if funct7 == 0b010_0000 => Opcode::SUB,
                    0b001 if funct7 == 0b000_0000 => Opcode::SLL,
                    0b010 if funct7 == 0b000_0000 => Opcode::SLT,
                    0b011 if funct7 == 0b000_0000 => Opcode::SLTU,
                    0b100 if funct7 == 0b000_0000 => Opcode::XOR,
                    0b101 if funct7 == 0b000_0000 => Opcode::SRL,
                    0b101 if funct7 == 0b010_0000 => Opcode::SRA,
                    0b110 if funct7 == 0b000_0000 => Opcode::OR,
                    0b111 if funct7 == 0b000_0000 => Opcode::AND,
                        _ => Err(Exception::IllegalInstruction(inst))?,
                };

                (opcode, EncodeType::RType)
            }
            0b0001111 => match funct3 {
                0b000 => (Opcode::FENCE, EncodeType::IType),
                0b001 => (Opcode::FENCE_I, EncodeType::IType),
                    _ => Err(Exception::IllegalInstruction(inst))?,
            }
            0b1110011 if inst.truncate(19, 7) == 0 => match funct12 {
                0b0000_0000_0000 => (Opcode::ECALL, EncodeType::IType),
                0b0000_0000_0001 => (Opcode::EBREAK, EncodeType::IType),
                0b0011_0000_0010 => (Opcode::MRET, EncodeType::IType),
                               _ => Err(Exception::IllegalInstruction(inst))?,
            }
            0b1110011 => match funct3 {
                0b001 => (Opcode::CSRRW, EncodeType::IType),
                0b010 => (Opcode::CSRRS, EncodeType::IType),
                0b011 => (Opcode::CSRRC, EncodeType::IType),
                0b101 => (Opcode::CSRRWI, EncodeType::IType),
                0b110 => (Opcode::CSRRSI, EncodeType::IType),
                0b111 => (Opcode::CSRRCI, EncodeType::IType),
                    _ => Err(Exception::IllegalInstruction(inst))?,
            }
            _ => Err(Exception::IllegalInstruction(inst))?,
        };

        Ok(Instruction { raw_code: inst, opcode, encode_type })
    }
    */

    fn rs1(&self) -> usize {
        match self.encode_type {
            EncodeType::RType |
            EncodeType::IType |
            EncodeType::SType |
            EncodeType::BType => self.raw_code.truncate(19, 15) as usize,
            tpe => panic!(make_panic_msg(tpe, "rs1"))
        }
    }

    fn rs2(&self) -> usize {
        match self.encode_type {
            EncodeType::RType |
            EncodeType::SType |
            EncodeType::BType => self.raw_code.truncate(24, 20) as usize,
            tpe => panic!(make_panic_msg(tpe, "rs2"))
        }
    }

    fn rd(&self) -> usize {
        match self.encode_type {
            EncodeType::RType |
            EncodeType::IType |
            EncodeType::UType |
            EncodeType::JType => self.raw_code.truncate(11, 7) as usize,
            tpe => panic!(make_panic_msg(tpe, "rd"))
        }
    }

    fn imm(&self) -> u32 {
        match self.encode_type {
            EncodeType::RType =>
                panic!(make_panic_msg(EncodeType::RType, "imm")),
            EncodeType::IType => {
                let truncated = self.raw_code.truncate(31, 20) as u32;
                truncated.sign_ext(11)
            }
            EncodeType::SType => {
                let upper = self.raw_code.truncate(31, 25) as u32;
                let lower = self.raw_code.truncate(11, 7) as u32;

                Bitwise::concat(&[lower, upper], &[5, 7]).sign_ext(11)
            }
            EncodeType::BType => {
                let raw_code = self.raw_code as u32;
                let bit12 = raw_code.extract(31);
                let bit11 = raw_code.extract(7);
                let bit10_5 = raw_code.truncate(30, 25);
                let bit4_1 = raw_code.truncate(11, 8);
                let bit0 = 0;

                Bitwise::concat(
                    &[bit0, bit4_1, bit10_5, bit11, bit12],
                    &[1, 4, 6, 1, 1]
                ).sign_ext(12)
            }
            EncodeType::UType => {
                let raw_code = self.raw_code as u32;
                let bit31_12 = raw_code.truncate(31, 12);
                let bit11_0 = 0;

                Bitwise::concat(&[bit11_0, bit31_12], &[12, 20]).sign_ext(31)
            }
            EncodeType::JType => {
                let raw_code = self.raw_code as u32;
                let bit20 = raw_code.extract(31);
                let bit19_12 = raw_code.truncate(19, 12);
                let bit11 = raw_code.extract(20);
                let bit10_1 = raw_code.truncate(30, 21);
                let bit0 = 0;

                Bitwise::concat(
                    &[bit0, bit10_1, bit11, bit19_12, bit20],
                    &[1, 10, 1, 8, 1]
                ).sign_ext(20)

            }
        }
    }

    fn lui(&self, core: &mut Core) -> Result<(), Exception> {
        core.ireg.write(
            self.rd(),
            self.imm(),
        );

        Ok(())
    }

    fn auipc(&self, core: &mut Core) -> Result<(), Exception> {
        core.ireg.write(
            self.rd(),
            self.imm().wrapping_add(core.pc),
        );

        Ok(())
    }

    fn jal(&self, core: &mut Core) -> Result<(), Exception> {
        let dest = self.imm().wrapping_add(core.pc);
        let next_pc = core.pc.wrapping_add(4);

        core.branch_manager.push_queue(dest);
        core.ireg.write(self.rd(), next_pc);

        Ok(())
    }

    fn jalr(&self, core: &mut Core) -> Result<(), Exception>{
        let rs1_value = core.ireg.read(self.rs1());
        let dest = self.imm().wrapping_add(rs1_value) & (std::u32::MAX ^ 1);
        let next_pc = core.pc.wrapping_add(4);

        core.branch_manager.push_queue(dest);
        core.ireg.write(self.rd(), next_pc);

        Ok(())
    }

    // execute branch instruction operation
    fn branch(&self, core: &mut Core, f: impl Fn(u32, u32) -> bool) -> Result<(), Exception> {
        let rs1_value = core.ireg.read(self.rs1());
        let rs2_value = core.ireg.read(self.rs2());

        let branch_dest =
            if f(rs1_value, rs2_value) {
                core.pc.wrapping_add(self.imm())
            } else {
                core.pc.wrapping_add(4)
            };

        core.branch_manager.push_queue(branch_dest);

        Ok(())
    }

    fn beq(&self, core: &mut Core) -> Result<(), Exception> { self.branch(core, |a, b| a == b) }
    fn bne(&self, core: &mut Core) -> Result<(), Exception> { self.branch(core, |a, b| a != b) }
    fn blt(&self, core: &mut Core) -> Result<(), Exception> {
        self.branch(core, |a, b| {
            let a = a as i32;
            let b = b as i32;

            a < b
        })
    }
    fn bge(&self, core: &mut Core) -> Result<(), Exception> {
        self.branch(core, |a, b| {
            let a = a as i32;
            let b = b as i32;

            a >= b
        })
    }
    fn bltu(&self, core: &mut Core) -> Result<(), Exception> { self.branch(core, |a, b| a < b) }
    fn bgeu(&self, core: &mut Core) -> Result<(), Exception> { self.branch(core, |a, b| a >= b) }

    fn load(&self, core: &mut Core, byte_count: u32, use_sign_ext: bool) -> Result<(), Exception> {
        let base_addr = core.ireg.read(self.rs1()).wrapping_add(self.imm());
        let data = (0..byte_count).map(|offset| {
            core.memory.read(base_addr.wrapping_add(offset)) as u32
        }).collect::<Vec<u32>>();


        let data = Bitwise::concat(&data, &vec![8; byte_count as usize]);
        let data =
            if use_sign_ext { data.sign_ext(8 * byte_count as u32 - 1) }
            else            { data };

        core.ireg.write(self.rd(), data);
        Ok(())
    }

    fn lb(&self, core: &mut Core) -> Result<(), Exception> { self.load(core, 1, true) }
    fn lh(&self, core: &mut Core) -> Result<(), Exception> { self.load(core, 2, true) }
    fn lw(&self, core: &mut Core) -> Result<(), Exception> { self.load(core, 4, true) }
    fn lbu(&self, core: &mut Core) -> Result<(), Exception> { self.load(core, 1, false) }
    fn lhu(&self, core: &mut Core) -> Result<(), Exception> { self.load(core, 2, false) }

    fn store(&self, core: &mut Core, byte_size: u32) -> Result<(), Exception> {
        let addr = core.ireg.read(self.rs1()).wrapping_add(self.imm());
        let data = core.ireg.read(self.rs2());
        (0..byte_size)
            .map(|index| data.truncate((index + 1) * 8 - 1, index * 8) as u8)
            .zip(0..)
            .for_each(|(data, index)| core.memory.write(addr.wrapping_add(index), data));

        Ok(())
    }

    fn sb(&self, core: &mut Core) -> Result<(), Exception> { self.store(core, 1) }
    fn sh(&self, core: &mut Core) -> Result<(), Exception> { self.store(core, 2) }
    fn sw(&self, core: &mut Core) -> Result<(), Exception> { self.store(core, 4) }

    fn rs1_imm_ops(&self, core: &mut Core, f: impl Fn(u32, u32) -> u32) -> Result<(), Exception> {
        let rs1_value = core.ireg.read(self.rs1());
        let imm_value = self.imm();
        let result = f(rs1_value, imm_value);

        core.ireg.write(self.rd(), result);

        Ok(())
    }

    fn addi(&self, core: &mut Core) -> Result<(), Exception> {
        self.rs1_imm_ops(core, |rs1, imm| rs1.wrapping_add(imm))
    }

    fn slti(&self, core: &mut Core) -> Result<(), Exception> {
        self.rs1_imm_ops(core, |rs1, imm| {
            let rs1 = rs1 as i32;
            let imm = imm as i32;

            (rs1 < imm) as u32
        })
    }

    fn sltiu(&self, core: &mut Core) -> Result<(), Exception> {
        self.rs1_imm_ops(core, |rs1, imm| {
            (rs1 < imm) as u32
        })
    }

    fn xori(&self, core: &mut Core) -> Result<(), Exception> {
        self.rs1_imm_ops(core, |rs1, imm| { rs1 ^ imm } )
    }

    fn ori(&self, core: &mut Core) -> Result<(), Exception> {
        self.rs1_imm_ops(core, |rs1, imm| { rs1 | imm } )
    }

    fn andi(&self, core: &mut Core) -> Result<(), Exception> {
        self.rs1_imm_ops(core, |rs1, imm| { rs1 & imm } )
    }

    fn slli(&self, core: &mut Core) -> Result<(), Exception> {
        self.rs1_imm_ops(core, |rs1, imm| {
            let shamt = imm.truncate(4, 0);
            rs1 << shamt
        })
    }

    fn srli(&self, core: &mut Core) -> Result<(), Exception> {
        self.rs1_imm_ops(core, |rs1, imm| {
            let shamt = imm.truncate(4, 0);
            rs1 >> shamt
        })
    }

    fn srai(&self, core: &mut Core) -> Result<(), Exception> {
        self.rs1_imm_ops(
            core,
            |rs1, imm| arithmetic_right_shift(rs1, imm),
        )
    }

    fn rs1_rs2_ops(&self, core: &mut Core, f: impl Fn(u32, u32) -> u32) -> Result<(), Exception> {
        let rs1_value = core.ireg.read(self.rs1());
        let rs2_value = core.ireg.read(self.rs2());
        let result = f(rs1_value, rs2_value);

        core.ireg.write(self.rd(), result);

        Ok(())
    }

    fn add(&self, core: &mut Core) -> Result<(), Exception> {
        self.rs1_rs2_ops(core, |rs1, rs2| rs1.wrapping_add(rs2))
    }

    fn sub(&self, core: &mut Core) -> Result<(), Exception> {
        self.rs1_rs2_ops(core, |rs1, rs2| rs1.wrapping_sub(rs2))
    }

    fn xor(&self, core: &mut Core) -> Result<(), Exception> {
        self.rs1_rs2_ops(core, |rs1, rs2| rs1 ^ rs2)
    }

    fn or(&self, core: &mut Core) -> Result<(), Exception> {
        self.rs1_rs2_ops(core, |rs1, rs2| rs1 | rs2)
    }

    fn and(&self, core: &mut Core) -> Result<(), Exception> {
        self.rs1_rs2_ops(core, |rs1, rs2| rs1 & rs2)
    }

    fn slt(&self, core: &mut Core) -> Result<(), Exception> {
        self.rs1_rs2_ops(core, |rs1, rs2| {
            let rs1 = rs1 as i32;
            let rs2 = rs2 as i32;

            (rs1 < rs2) as u32
        })
    }

    fn sltu(&self, core: &mut Core) -> Result<(), Exception> {
        self.rs1_rs2_ops(core, |rs1, rs2| {
            (rs1 < rs2) as u32
        })
    }

    fn sll(&self, core: &mut Core) -> Result<(), Exception> {
        self.rs1_rs2_ops(core, |rs1, rs2| {
            rs1 << rs2.truncate(4, 0)
        })
    }

    fn srl(&self, core: &mut Core) -> Result<(), Exception> {
        self.rs1_rs2_ops(core, |rs1, rs2| {
            rs1 >> rs2.truncate(4, 0)
        })
    }

    fn sra(&self, core: &mut Core) -> Result<(), Exception> {
        self.rs1_rs2_ops(
            core,
            |rs1, rs2| arithmetic_right_shift(rs1, rs2.truncate(4, 0))
        )
    }

    fn csr_manipulate(
        &self,
        core: &mut Core,
        read: impl Fn(&mut Core, usize) -> Result<u32, Exception>,
        write: impl Fn(&mut Core, usize, u32, u32) -> Result<(), Exception>,
        get_src: impl Fn(&mut Core) -> u32,
    ) -> Result<(), Exception> {
        let addr = self.imm().truncate(11, 0) as usize;
        let csr = read(core, addr)?;
        let src = get_src(core);
        let rd = self.rd();

        core.ireg.write(rd, csr);

        write(core, addr, csr, src)
    }

    fn csr_manipulate_uimm(
        &self,
        core: &mut Core,
        read: impl Fn(&mut Core, usize) -> Result<u32, Exception>,
        write: impl Fn(&mut Core, usize, u32, u32) -> Result<(), Exception>,
    ) -> Result<(), Exception> {
        self.csr_manipulate(core, read, write, |_| self.rs1() as u32)
    }


    fn csr_manipulate_rs1(
        &self,
        core: &mut Core,
        read: impl Fn(&mut Core, usize) -> Result<u32, Exception>,
        write: impl Fn(&mut Core, usize, u32, u32) -> Result<(), Exception>
    ) -> Result<(), Exception> {
        self.csr_manipulate(core, read, write, |core| core.ireg.read(self.rs1()))
    }

    fn csrrw(&self, core: &mut Core) -> Result<(), Exception> {
        self.csr_manipulate_rs1(
            core,
            |core, addr| -> Result<u32, Exception> {
                if self.rd() == 0 { Ok(0) }
                else { core.csr.read(addr, self.raw_code) }
            },
            |core, addr, _csr, rs1| -> Result<(), Exception>{
                core.csr.write(addr, rs1, self.raw_code)
            }
        )
    }

    fn csrrs(&self, core: &mut Core) -> Result<(), Exception> {
        self.csr_manipulate_rs1(
            core,
            |core, addr| -> Result<u32, Exception> {
                core.csr.read(addr, self.raw_code)
            },
            |core, addr, csr, rs1| -> Result<(), Exception> {
                if self.rs1() == 0 { Ok(()) }
                else { core.csr.write(addr, csr | rs1, self.raw_code) }
            }
        )
    }

    fn csrrc(&self, core: &mut Core) -> Result<(), Exception>{
        self.csr_manipulate_rs1(
            core,
            |core, addr| -> Result<u32, Exception> {
                core.csr.read(addr, self.raw_code)
            },
            |core, addr, csr, rs1| -> Result<(), Exception> {
                if self.rs1() == 0 { Ok(()) }
                else { core.csr.write(addr, csr & !rs1, self.raw_code) }
            }
        )
    }

    fn csrrwi(&self, core: &mut Core) -> Result<(), Exception> {
        self.csr_manipulate_uimm(
            core,
            |core, addr| -> Result<u32, Exception> {
                if self.rd() == 0 { Ok(0) }
                else { core.csr.read(addr, self.raw_code) }
            },
            |core, addr, _csr, uimm| -> Result<(), Exception>{
                core.csr.write(addr, uimm, self.raw_code)
            }
        )
    }

    fn csrrsi(&self, core: &mut Core) -> Result<(), Exception> {
        self.csr_manipulate_uimm(
            core,
            |core, addr| -> Result<u32, Exception> {
                core.csr.read(addr, self.raw_code)
            },
            |core, addr, csr, uimm| -> Result<(), Exception> {
                if self.rs1() == 0 { Ok(()) }
                else { core.csr.write(addr, csr | uimm, self.raw_code) }
            }
        )
    }

    fn csrrci(&self, core: &mut Core) -> Result<(), Exception> {
        self.csr_manipulate_uimm(
            core,
            |core, addr| -> Result<u32, Exception> {
                core.csr.read(addr, self.raw_code)
            },
            |core, addr, csr, uimm| -> Result<(), Exception> {
                if self.rs1() == 0 { Ok(()) }
                else { core.csr.write(addr, csr & !uimm, self.raw_code) }
            }
        )
    }

    // FENCE and FENCE_I instructions does not do anything
    fn fence(&self, _core: &mut Core) -> Result<(), Exception> { Ok(()) }
    fn fence_i(&self, _core: &mut Core) -> Result<(), Exception> { Ok(()) }

    fn ecall(&self, _core: &mut Core) -> Result<(), Exception> {
        // for now, there is only m-mode, so no need to select environmental call patterns.
        Err(Exception::EnvironmentalCallMMode)
    }
    fn ebreak(&self, core: &mut Core) -> Result<(), Exception> { Err(Exception::Breakpoint(core.pc)) }

    fn mret(&self, core: &mut Core) -> Result<(), Exception> {
        let _ = core.csr.get_mpp(); // this core runs only on m-mode for now, so this value is thrown away.
        core.csr.set_mpp(0b11);

        let mpie = core.csr.get_mpie();
        core.csr.set_mpie(false);
        core.csr.set_mie(mpie == 1);

        let epc = core.csr.read(M_E_PC, 0).unwrap();
        core.pc = epc - 4;

        Ok(())
    }

    pub fn exec(&self, core: &mut Core) -> Result<(), Exception> {
        match self.opcode {
            Opcode::LUI => self.lui(core),
            Opcode::AUIPC => self.auipc(core),
            Opcode::JAL => self.jal(core),
            Opcode::JALR => self.jalr(core),
            Opcode::BEQ => self.beq(core),
            Opcode::BNE => self.bne(core),
            Opcode::BLT => self.blt(core),
            Opcode::BGE => self.bge(core),
            Opcode::BLTU => self.bltu(core),
            Opcode::BGEU => self.bgeu(core),
            Opcode::LB => self.lb(core),
            Opcode::LH => self.lh(core),
            Opcode::LW => self.lw(core),
            Opcode::LBU => self.lbu(core),
            Opcode::LHU => self.lhu(core),
            Opcode::SB => self.sb(core),
            Opcode::SH => self.sh(core),
            Opcode::SW => self.sw(core),
            Opcode::ADDI => self.addi(core),
            Opcode::SLTI => self.slti(core),
            Opcode::SLTIU => self.sltiu(core),
            Opcode::XORI => self.xori(core),
            Opcode::ORI => self.ori(core),
            Opcode::ANDI => self.andi(core),
            Opcode::SLLI => self.slli(core),
            Opcode::SRLI => self.srli(core),
            Opcode::SRAI => self.srai(core),
            Opcode::ADD => self.add(core),
            Opcode::SUB => self.sub(core),
            Opcode::SLL => self.sll(core),
            Opcode::SLT => self.slt(core),
            Opcode::SLTU => self.sltu(core),
            Opcode::XOR => self.xor(core),
            Opcode::SRL => self.srl(core),
            Opcode::SRA => self.sra(core),
            Opcode::OR => self.or(core),
            Opcode::AND => self.and(core),
            Opcode::FENCE => self.fence(core),
            Opcode::FENCE_I => self.fence_i(core),
            Opcode::ECALL => self.ecall(core),
            Opcode::EBREAK => self.ebreak(core),
            Opcode::CSRRW => self.csrrw(core),
            Opcode::CSRRS => self.csrrs(core),
            Opcode::CSRRC => self.csrrc(core),
            Opcode::CSRRWI => self.csrrwi(core),
            Opcode::CSRRSI => self.csrrsi(core),
            Opcode::CSRRCI => self.csrrci(core),
            Opcode::MRET => self.mret(core),
        }
    }
}

fn make_panic_msg(name: EncodeType, field: &str) -> String {
    format!("{} does not have {} field", name, field)
}

fn arithmetic_right_shift(value: u32, shamt: u32) -> u32 {
    let shamt = shamt.truncate(4, 0);

    if value.extract(31) == 1 {
        let length = 32 - shamt;
        let ones = std::u32::MAX as u32;
        let mask = 1_u32.checked_shl(length).unwrap_or(0).wrapping_sub(1);

        (value >> shamt) | (mask ^ ones)
    } else {
        value >> shamt
    }
}

#[derive(Clone, Copy, Debug, PartialEq)]
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

/*
#[allow(non_camel_case_types)]
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
    FENCE_I,
    ECALL,
    EBREAK,
    CSRRW,
    CSRRS,
    CSRRC,
    CSRRWI,
    CSRRSI,
    CSRRCI,
    MRET,
}
*/

macro_rules! opcode_list {
    ($({ $opcode: ident, $encode_type: ident, op: $op: literal $(, f3: $f3: literal)? $(, f7: $f7: literal)? $(, f12: $f12: literal)? $(, [ $upper: literal, $lower: literal ] : $expect : literal),* $(,)?}),+) => {
        impl Instruction {
            pub fn new(inst: u32) -> Result<Instruction, Exception> {
                let opcode = inst.truncate(6, 0);
                let funct3 = inst.truncate(14, 12);
                let funct7 = inst.truncate(31, 25);
                let funct12 = inst.truncate(31, 20);

                match inst {
                    $(
                        _ if opcode == $op $(&& funct3 == $f3)? $(&& funct7 == $f7)? $(&& funct12 == $f12)? $(&& inst.truncate($upper, $lower) == $expect)* => {
                            return Ok(Instruction {
                                raw_code: inst,
                                opcode: Opcode::$opcode,
                                encode_type: EncodeType::$encode_type
                            })
                        }
                    )+
                    _ => return Err(Exception::IllegalInstruction(inst)),
                }
            }
        }

        #[allow(non_camel_case_types)]
        #[derive(Clone, Copy, Debug, PartialEq)]
        enum Opcode {
            $(
                $opcode,
            )+
        }

        impl fmt::Display for Opcode {
            fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
                write!(f, "{}", format!("{:?}", self).to_lowercase())
            }
        }
    }
}

opcode_list!(
    { LUI, UType, op: 0b0110111, },
    { AUIPC, UType, op: 0b0010111, },
    { JAL, JType, op: 0b1101111, },
    { JALR, IType, op: 0b1101111, f3: 0b000, },
    { BEQ, BType, op: 0b1100011, f3: 0b000, },
    { BNE, BType, op: 0b1100011, f3: 0b001, },
    { BLT, BType, op: 0b1100011, f3: 0b100, },
    { BGE, BType, op: 0b1100011, f3: 0b101, },
    { BLTU, BType, op: 0b1100011, f3: 0b110, },
    { BGEU, BType, op: 0b1100011, f3: 0b111, },
    { LB, IType, op: 0b0000011, f3: 0b000, },
    { LH, IType, op: 0b0000011, f3: 0b001, },
    { LW, IType, op: 0b0000011, f3: 0b010, },
    { LBU, IType, op: 0b0000011, f3: 0b100, },
    { LHU, IType, op: 0b0000011, f3: 0b101, },
    { SB, IType, op: 0b0100011, f3: 0b000, },
    { SH, IType, op: 0b0100011, f3: 0b001, },
    { SW, IType, op: 0b0100011, f3: 0b010, },
    { ADDI, IType, op: 0b0010011, f3: 0b000, },
    { SLTI, IType, op: 0b0010011, f3: 0b010, },
    { SLTIU, IType, op: 0b0010011, f3: 0b011, },
    { XORI, IType, op: 0b0010011, f3: 0b100, },
    { ORI, IType, op: 0b0010011, f3: 0b110, },
    { ANDI, IType, op: 0b0010011, f3: 0b111, },
    { SLLI, IType, op: 0b0010011, f3: 0b001, f7: 0b000_0000, },
    { SRLI, IType, op: 0b0010011, f3: 0b101, f7: 0b000_0000, },
    { SRAI, IType, op: 0b0010011, f3: 0b101, f7: 0b010_0000, },
    { ADD, RType, op: 0b0110011, f3: 0b000, f7: 0b000_0000, },
    { SUB, RType, op: 0b0110011, f3: 0b000, f7: 0b010_0000, },
    { SLL, RType, op: 0b0110011, f3: 0b001, f7: 0b000_0000, },
    { SLT, RType, op: 0b0110011, f3: 0b010, f7: 0b000_0000, },
    { SLTU, RType, op: 0b0110011, f3: 0b011, f7: 0b000_0000, },
    { XOR, RType, op: 0b0110011, f3: 0b100, f7: 0b000_0000, },
    { SRL, RType, op: 0b0110011, f3: 0b101, f7: 0b000_0000, },
    { SRA, RType, op: 0b0110011, f3: 0b101, f7: 0b010_0000, },
    { OR, RType, op: 0b0110011, f3: 0b110, f7: 0b000_0000, },
    { AND, RType, op: 0b0110011, f3: 0b111, f7: 0b000_0000, },
    { FENCE, IType, op: 0b0001111, f3: 0b000, },
    { FENCE_I, IType, op: 0b0001111, f3: 0b001, },
    { ECALL, IType, op: 0b1110011, f12: 0b0000_0000_0000, [19, 7]: 0, },
    { EBREAK, IType, op: 0b1110011, f12: 0b0000_0000_0001, [19, 7]: 0, },
    { MRET, IType, op: 0b1110011, f12: 0b0000_0000_0001, [19, 7]: 0, },
    { CSRRW, IType, op: 0b1110011, f3: 0b001, },
    { CSRRS, IType, op: 0b1110011, f3: 0b010, },
    { CSRRC, IType, op: 0b1110011, f3: 0b011, },
    { CSRRWI, IType, op: 0b1110011, f3: 0b101, },
    { CSRRSI, IType, op: 0b1110011, f3: 0b110, },
    { CSRRCI, IType, op: 0b1110011, f3: 0b111, }
);

#[cfg(test)]
mod test {
    use super::{
        Instruction,
        Opcode,
        EncodeType,
    };

    #[test]
    fn make_add_inst() {
        let inst = Instruction::test_decode(0x0000_0033).unwrap();
        assert_eq!(inst.opcode, Opcode::ADD);
        assert_eq!(inst.encode_type, EncodeType::RType);
    }
}