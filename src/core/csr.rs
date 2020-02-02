use std::collections::HashMap;
use super::Bitwise;
use crate::util::exception::Exception;

pub struct CSRFile {
    csrs: HashMap<usize, u32>,
    performance_counter: HashMap<usize, u64>,
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
            performance_counter.insert(addr, 0);
        }

        csrs.insert(M_ISA, Bitwise::concat(&[1 << 8, 0, 1], &[26, 4, 2]));

        CSRFile {
            csrs,
            performance_counter,
        }
    }

    pub fn write(&mut self, addr: usize, value: u32, inst: u32) -> Result<(), Exception>{
        if addr & 0b1100_0000_0000 > 0 { return Err(Exception::IllegalInstruction(inst)) }

        match addr {
            M_STATUS => self.write_csr(M_STATUS, value, 0x0000_1888, "mstatus"),
            M_ISA => self.write_csr(M_ISA, value, 0, "misa"),
            M_E_DELEG => panic!("medeleg is not implemented"),
            M_I_DELEG => panic!("mideleg is not implemented"),
            M_IE => self.write_csr(M_IE, value, 0x0000_0888, "mie"),
            M_T_VEC => self.write_csr(M_T_VEC, value, 0xFFFF_FFFD, "mtvec"),
            M_COUNTER_EN => self.write_csr(M_COUNTER_EN, value, 0xFFFF_FFFF, "mcounteren"),
            M_SCRATCH => self.write_csr(M_SCRATCH, value, 0xFFFF_FFFF, "mscratch"),
            M_E_PC => self.write_csr(M_E_PC, value, 0xFFFF_FFFC, "mepc"),
            M_CAUSE => self.write_csr(M_CAUSE, value, 0xFFFF_FFFF, "mcause"),
            M_T_VAL => self.write_csr(M_T_VAL, value, 0xFFFF_FFFF, "mtval"),
            M_IP => self.write_csr(M_IP, value, 0, "mip"),
            M_CYCLE => self.write_hpm_counter(M_CYCLE, value, "mcycle"),
            M_INST_RET => self.write_hpm_counter(M_INST_RET, value, "minstret"),
            M_CYCLE_H => self.write_hpm_counterh(M_CYCLE, value, "mcycleh"),
            M_INST_RET_H => self.write_hpm_counterh(M_INST_RET, value, "minstreth"),
            addr if is_hpm_counter_range(addr) => self.write_hpm_counter(addr, value, "mhpmcounter"),
            addr if is_hpm_counter_h_range(addr) => self.write_hpm_counterh(addr, value, "mhpmcounterh"),
            addr if is_hpm_event_range(addr) => self.write_hpm_event(addr, value, "mhpmevent"),
            _ => Err(Exception::IllegalInstruction(inst))?,
        }

        Ok(())
    }

    fn write_csr(&mut self, addr: usize, value: u32, mask: u32, name: &str) {
        let masked_value = value & mask;
        self.csrs.insert(addr, masked_value);
    }

    fn write_hpm_counter(&mut self, addr: usize, value: u32, name: &str) {
        let counter = self.performance_counter[&addr];
        let counter = counter & 0xFFFF_FFFF_0000_0000;
        let value = counter | (value as u64);

        self.performance_counter.insert(addr, value);
    }

    fn write_hpm_counterh(&mut self, addr: usize, value: u32, name: &str) {
        let addr = addr & !0x80;
        let counter = self.performance_counter[&addr];
        let counter = counter & 0x0000_0000_FFFF_FFFF;
        let value = counter | ((value as u64) << 32);

        self.performance_counter.insert(addr, value);
    }

    fn write_hpm_event(&mut self, addr: usize, value: u32, name: &str) {
        self.csrs.insert(addr, value);
    }

    pub fn read(&self, addr: usize, inst: u32) -> Result<u32, Exception> {
        let value = match self.csrs.get(&addr) {
            Some(&value) => value,
            None => match addr {
                M_CYCLE => self.read_hpm_counter(addr),
                M_INST_RET => self.read_hpm_counter(addr),
                M_CYCLE_H => self.read_hpm_counter_h(addr),
                M_INST_RET_H => self.read_hpm_counter_h(addr),
                addr if is_hpm_counter_range(addr) => self.read_hpm_counter(addr),
                addr if is_hpm_counter_h_range(addr) => self.read_hpm_counter_h(addr),
                _ => Err(Exception::IllegalInstruction(inst))?
            }
        };

        Ok(value)
    }

    fn read_hpm_counter(&self, addr: usize) -> u32 {
        let counter = self.performance_counter[&addr];

        (counter & 0x0000_0000_FFFF_FFFF) as u32
    }

    fn read_hpm_counter_h(&self, addr: usize) -> u32 {
        let counter = self.performance_counter[&addr];

        (counter >> 32) as u32
    }

    pub fn make_exception_vector(&self, e: Exception) -> u32 {
        let tvec = self.csrs.get(&M_T_VEC).unwrap();
        let mode = tvec.truncate(1, 0);
        let code = e.get_exception_code();
        let base = tvec.truncate(31, 2) << 2;

        match mode {
            0 => base,
            1 if e.is_interrupt() => base,
            1 => base + 4 * code,
            _ => panic!("unexpected tvec mode({}). this is implementation bug.", mode),
        }
    }

    pub fn get_mie(&self) -> u32 {
        self.csrs[&M_STATUS].extract(3)
    }

    pub fn set_mie(&mut self, value: bool) {
        let mstatus = self.csrs[&M_STATUS] & !(1 << 3);
        let mstatus = mstatus | ((value as u32) << 3);
        *self.csrs.entry(M_STATUS).or_insert(no_csr("mstatus")) = mstatus;
    }

    pub fn get_mpie(&self) -> u32 {
        self.csrs[&M_STATUS].extract(7)
    }

    pub fn set_mpie(&mut self, value: bool) {
        let mstatus = self.csrs[&M_STATUS] & !(1 << 7);
        let mstatus = mstatus | ((value as u32) << 7);
        *self.csrs.entry(M_STATUS).or_insert(no_csr("mstatus")) = mstatus;
    }

    pub fn get_mpp(&self) -> u32 {
        self.csrs[&M_STATUS].truncate(12, 11)
    }

    pub fn set_mpp(&mut self, value: u32) {
        let mstatus = self.csrs[&M_STATUS] & !(3 << 11);
        let mpp = value & 3;
        let mstatus = mstatus | (mpp << 11);

        *self.csrs.entry(M_STATUS).or_insert(no_csr("mstatus")) = mstatus;
    }
}

fn no_csr(csr: &str) -> ! {
    panic!("implementation error there is no {}", csr)
}

pub const M_VENDOR_ID: usize = 0xF11;
pub const M_ARCH_ID: usize = 0xF12;
pub const M_IMP_ID: usize = 0xF13;
pub const M_HARD_ID: usize = 0xF14;

pub const M_STATUS: usize = 0x300;
pub const M_ISA: usize = 0x301;
pub const M_E_DELEG: usize = 0x302;
pub const M_I_DELEG: usize = 0x303;
pub const M_IE: usize = 0x304;
pub const M_T_VEC: usize = 0x305;
pub const M_COUNTER_EN: usize = 0x306;

pub const M_COUNT_INHIBIT: usize = 0x320;
pub const M_HPM_EVENT_BASE: usize = 0x320;

pub const M_SCRATCH: usize = 0x340;
pub const M_E_PC: usize = 0x341;
pub const M_CAUSE: usize = 0x342;
pub const M_T_VAL: usize = 0x343;
pub const M_IP: usize = 0x344;

pub const M_CYCLE: usize = 0xB00;
pub const M_INST_RET: usize = 0xB02;
pub const M_HPM_COUNTER_BASE: usize = 0xB00;
pub const M_CYCLE_H: usize = 0xB80;
pub const M_INST_RET_H: usize = 0xB82;
pub const M_HPM_COUNTER_H_BASE: usize = 0xB80;

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