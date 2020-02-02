use std::collections::HashMap;
use super::Bitwise;
use crate::core::csr::CSRAddr::{Mvendorid, Marchid, Mimpid, Mhardid, Mideleg, Mcounteren};

pub struct CSRFile {
    csrs: HashMap<usize, u32>,
    performance_counter: HashMap<usize, u32>,
}

impl CSRFile {
    pub fn new() -> CSRFile {
        let mut csrs = HashMap::new();

        for &addr in CSR_ADDR_LIST.iter() {
            csrs.insert(addr, 0);
        }

        for addr in M_HPM_EVENT_BASE + 0x03..M_HPM_EVENT_BASE + 0x20 {
            csrs.insert(addr, 0);
        }

        let mut performance_counter = HashMap::new();
        performance_counter.insert(M_CYCLE, 0);
        performance_counter.insert(M_INST_RET, 0);
        for addr in M_HPM_COUNTER_BASE + 0x03..M_HPM_COUNTER_BASE + 0x20 {
            performance_coutner.insert(&addr, 0);
        }

        csrs[M_ISA] = Bitwise::concat(&[1 << 8, 0, 1], &[26, 4, 2]);

        CSRFile {
            csrs,
            performance_counter,
        }
    }

    pub fn write(&mut self, addr: usize, value: u32) {
        if addr & 0b1100_0000_0000 > 0 { panic!("write to read only csr")}

        match addr {
            M_STATUS => self.write_mstatus(value),
            M_ISA => self.write_misa(value),
            M_E_DELEG => panic!("medeleg is not implemented"),
            M_I_DELEG => panic!("mideleg is not implemented"),
            M_IE => self.write_mie(value),
            M_T_VEC => self.write_mtvec(value),
            M_COUNTER_EN => self.write_mcounteren(value),
            M_SCRATCH => self.write_mscratch(value),
            M_E_PC => self.write_mepc(value),
            M_CAUSE => self.write_mcause(value),
            M_T_VAL => self.write_mtval(value),
            M_IP => self.write_mip(value),
            M_CYCLE => self.write_hpm_counter(M_CYCLE, value),
            M_INST_RET => self.write_hpm_counter(M_INST_RET, value),
            M_CYCLE_H => self.write_hpm_counterh(M_CYCLE_H, value),
            M_INST_RET_H => self.write_hpm_counterh(M_INST_RET_H, value),
            addr if is_hpm_counter_range(addr) => self.write_hpm_counter(addr, value),
            addr if is_hpm_counterh_range(addr) => self.write_hpm_counterh(addr, value),
            addr if is_hpm_event_range(addr) => self.write_hpm_event(addr, value),
            addr => println!("0x{:03x} is invalid address", addr),
        }
    }

    fn write_mstatus(&mut self, value: u32) {
        let hardwired_mask = 0x0000_1888;
        let masked_value = value & hardwired_mask;

        self.csrs[M_STATUS] = masked_value;
    }

    fn write_misa(&mut self, value: u32) {
        let hardwired_mask = 0;
        let masked_value = value & hardwired_mask;

        self.csrs[M_ISA] = masked_value;
    }

    fn write_mie(&mut self, value: u32) {
        let hardwired_mask = 0x0000_0888;
        let masked_value = value & hardwired_mask;

        self.csrs[M_IE] = masked_value;
    }

    fn write_mtvec(&mut self, value: u32) {
        let hardwired_mask = 0xFFFF_FFFD;
        let masked_value = value & hardwired_mask;

        self.csrs[M_T_VEC] = masked_value;
    }

    fn write_mcounteren(&mut self, value: u32) {
        self.csrs[M_COUNTER_EN] = value
    }

    fn write_mscratch(&mut self, value: u32) {
        self.csrs[M_SCRATCH] = value
    }

    fn write_mepc(&mut self, value: u32) {
        let hardwired_mask = 0xFFFF_FFFC;
        let masked_value = value & hardwired_mask;

        self.csrs[M_E_PC] = masked_value;
    }

    fn write_mcause(&mut self, value: u32) {
        self.csrs[M_CAUSE] = value;
    }

    fn write_mtval(&mut self, value: u32) {
        self.csrs[M_T_VAL] = value;
    }

    fn write_mip(&mut self, value: u32) {
        let mask = 0x0000_0000;
        let masked_value = value & mask;

        self.csrs[M_IP] = masked_value;
    }

    fn write_hpm_counter(&mut self, addr: usize, value: u32) {
        let counter = self.performance_counter[addr];
        let counter = counter & 0xFFFF_FFFF_0000_0000;
        let value = counter | (value as u64);

        self.performance_counter[addr] = value;
    }

    fn write_hpm_counterh(&mut self, addr: usize, value: u32) {
        let counter = self.performance_counter[addr];
        let counter = counter & 0x0000_0000_FFFF_FFFF;
        let value = counter | ((value as u64) << 32);

        self.performance_counter[addr] = value;
    }

    fn write_hpm_event(&mut self, addr: usize, value: u32) {
        self.csrs[addr] = value;
    }

    pub fn read(addr: usize) -> u32 {

    }
}

const M_VENDOR_ID: usize = 0xF11;
const M_ARCH_ID: usize = 0xF12;
const M_IMP_ID: usize = 0xF13;
const M_HARD_ID: usize = 0xF14;

const M_STATUS: usize = 0x300;
const M_ISA: usize = 0x301;
const M_E_DELEG: usize = 0x302;
const M_I_DELEG: usize = 0x303;
const M_IE: usize = 0x304;
const M_T_VEC: usize = 0x305;
const M_COUNTER_EN: usize = 0x306;

const M_COUNT_INHIBIT: usize = 0x320;
const M_HPM_EVENT_BASE: usize = 0x320;

const M_SCRATCH: usize = 0x340;
const M_E_PC: usize = 0x341;
const M_CAUSE: usize = 0x342;
const M_T_VAL: usize = 0x343;
const M_IP: usize = 0x344;

const M_CYCLE: usize = 0xB00;
const M_INST_RET: usize = 0xB02;
const M_HPM_COUNTER_BASE: usize = 0xB00;
const M_CYCLE_H: usize = 0xB80;
const M_INST_RET_H: usize = 0xB82;
const M_HPM_COUNTER_H_BASE: usize = 0xB80;

fn is_hpm_counter_range(addr: usize) -> bool {
    addr >= M_HPM_COUNTER_BASE + 0x03 && addr < M_HPM_COUNTER_BASE + 0x20
}

fn is_hpm_counter_h_range(addr: usize) -> bool {
    addr >= M_HPM_COUNTER_H_BASE + 0x03 && addr < M_HPM_COUNTER_H_BASE + 0x20
}

fn is_hpm_event_range(addr: usize) -> bool {
    addr >= M_HPM_EVENT_BASE + 0x03 && addr < M_HPM_EVENT_BASE + 0x20
}

const CSR_ADDR_LIST: [usize; 21] = [
    M_VENDOR_ID,
    M_ARCH_ID,
    M_IMP_ID,
    M_HARD_ID,
    M_STATUS,
    M_ISA,
    M_E_DELEG,
    M_I_DELEG,
    M_IE,
    M_T_VEC,
    M_COUNTER_EN,
    M_COUNT_INHIBIT,
    M_SCRATCH,
    M_E_PC,
    M_CAUSE,
    M_T_VAL,
    M_IP,
    M_CYCLE,
    M_INST_RET,
    M_CYCLE_H,
    M_INST_RET_H,
];