use super::super::bitwise::Bitwise;

trait EncodingType {
    fn name(&self) -> String;
    fn rs1(&self) -> u8 { panic!(make_panic_msg(self.name(), String::from("rs1"))) }
    fn rs2(&self) -> u8 { panic!(make_panic_msg(self.name(), String::from("rs2"))) }
    fn rd(&self) -> u8 { panic!(make_panic_msg(self.name(), String::from("rd"))) }
    fn imm(&self) -> u32 { panic!(make_panic_msg(self.name(), String::from("imm"))) }
    fn funct3(&self) -> u8 { panic!(make_panic_msg(self.name(), String::from("funct3"))) }
    fn funct7(&self) -> u8 { panic!(make_panic_msg(self.name(), String::from("funct7"))) }
}

fn make_panic_msg(name: String, field: String) -> String {
    format!("{} does not have {} field", name, field)
}

pub fn rtype(inst: u32) -> RType {
    let rd = inst.truncate(11, 7) as u8;
    let rs1 = inst.truncate(19, 15) as u8;
    let rs2 = inst.truncate(24, 20) as u8;
    let funct3 = inst.truncate(14, 12) as u8;
    let funct7 = inst.truncate(31, 25) as u8;

    RType { rd, rs1, rs2, funct3, funct7 }
}

pub struct RType {
    rs1: u8,
    rs2: u8,
    rd: u8,
    funct3: u8,
    funct7: u8,
}

impl EncodingType for RType {
    fn name(&self) -> String { String::from("R-Type") }
    fn rs1(&self) -> u8 { self.rs1 }
    fn rs2(&self) -> u8 { self.rs2 }
    fn rd(&self) -> u8 { self.rd }
    fn funct3(&self) -> u8 { self.funct3 }
    fn funct7(&self) -> u8 { self.funct7 }
}

pub struct IType {
    rs1: u8,
    rd: u8,
    imm: u32,
    funct3: u8,
}

pub fn itype(inst: u32) -> IType {
    let rd = inst.truncate(11, 7) as u8;
    let rs1 = inst.truncate(19, 15) as u8;
    let funct3 = inst.truncate(14, 12) as u8;
    let imm = inst.truncate(31, 20).sign_ext(11, 31);

    IType { rd, rs1, funct3, imm }
}

impl EncodingType for IType {
    fn name(&self) -> String { String::from("I-Type") }
    fn rs1(&self) -> u8 { self.rs1 }
    fn rd(&self) -> u8 { self.rd }
    fn imm(&self) -> u32 { self.imm }
    fn funct3(&self) -> u8 { self.funct3 }
}

pub struct SType {
    rs1: u8,
    rs2: u8,
    imm: u32,
    funct3: u8,
}

impl EncodingType for SType {
    fn name(&self) -> String { String::from("S-Type") }
    fn rs1(&self) -> u8 { self.rs1 }
    fn rs2(&self) -> u8 { self.rs2 }
    fn imm(&self) -> u32 { self.imm }
    fn funct3(&self) -> u8 { self.funct3 }
}

pub struct BType {
    rs1: u8,
    rs2: u8,
    imm: u32,
    funct3: u8,
}

impl EncodingType for BType {
    fn name(&self) -> String { String::from("B-Type") }
    fn rs1(&self) -> u8 { self.rs1 }
    fn rs2(&self) -> u8 { self.rs2 }
    fn imm(&self) -> u32 { self.imm }
    fn funct3(&self) -> u8 { self.funct3 }
}

pub struct UType {
    rd: u8,
    imm: u32,
}

impl EncodingType for UType {
    fn name(&self) -> String { String::from("U-Type") }
    fn rd(&self) -> u8 { self.rd }
    fn imm(&self) -> u32 { self.imm }
}

struct JType {
    rd: u8,
    imm: u32,
}

impl EncodingType for JType {
    fn name(&self) -> String { String::from("J-Type") }
    fn rd(&self) -> u8 { self.rd }
    fn imm(&self) -> u32 { self.imm }
}