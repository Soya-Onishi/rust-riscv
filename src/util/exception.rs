use super::super::core::csr::*;

#[derive(Debug, Clone, Copy)]
pub enum Exception {
    UserSoftwareInterrupt,
    SupervisorSoftwareInterrupt,
    MachineSoftwareInterrupt,

    UserTimerInterrupt,
    SupervisorTimerInterrupt,
    MachineTimerInterrupt,

    UserExternalInterrupt,
    SupervisorExternalInterrupt,
    MachineExternalInterrupt,

    InstructionAddressMisaligned(u32),
    InstructionAccessFault,

    IllegalInstruction(u32),

    Breakpoint(u32),

    LoadAddressMisaligned(u32),
    LoadAccessFault,
    StoreAddressMisaligned(u32),
    StoreAccessFault,

    EnvironmentalCallUMode,
    EnvironmentalCallSMode,
    EnvironmentalCallMMode,

    InstructionPageFault(u32),
    LoadPageFault(u32),
    StorePageFault(u32),
}

use Exception::*;
impl Exception {
    pub fn get_exception_code(self) -> u32 {
        use Exception::*;

        match self {
            UserSoftwareInterrupt => 0,
            SupervisorSoftwareInterrupt => 1,
            MachineSoftwareInterrupt => 3,
            UserTimerInterrupt => 4,
            SupervisorTimerInterrupt => 5,
            MachineTimerInterrupt => 7,
            UserExternalInterrupt => 8,
            SupervisorExternalInterrupt => 9,
            MachineExternalInterrupt => 11,
            InstructionAddressMisaligned(_) => 0,
            InstructionAccessFault => 1,
            IllegalInstruction(_) => 2,
            Breakpoint(_) => 3,
            LoadAddressMisaligned(_) => 4,
            LoadAccessFault => 5,
            StoreAddressMisaligned(_) => 6,
            StoreAccessFault => 7,
            EnvironmentalCallUMode => 8,
            EnvironmentalCallSMode => 9,
            EnvironmentalCallMMode => 11,
            InstructionPageFault(_) => 12,
            LoadPageFault(_) => 13,
            StorePageFault(_) => 15,
        }
    }

    pub fn is_interrupt(self) -> bool {
        match self {
            UserSoftwareInterrupt => true,
            SupervisorSoftwareInterrupt => true,
            MachineSoftwareInterrupt => true,
            UserTimerInterrupt => true,
            SupervisorTimerInterrupt => true,
            MachineTimerInterrupt => true,
            UserExternalInterrupt => true,
            SupervisorExternalInterrupt => true,
            MachineExternalInterrupt => true,
            _ => false,
        }
    }

    pub fn get_cause(self) -> u32 {
        let is_interrupt = self.is_interrupt() as u32;
        let code = self.get_exception_code();

        code | (is_interrupt << 31)
    }

    pub fn get_tval(self) -> u32 {
        match self {
            InstructionAddressMisaligned(v) => v,
            IllegalInstruction(v) => v,
            Breakpoint(v) => v,
            LoadAddressMisaligned(v) => v,
            StoreAddressMisaligned(v) => v,
            InstructionPageFault(v) => v,
            LoadPageFault(v) => v,
            StorePageFault(v) => v,
            _ => 0,
        }
    }
}