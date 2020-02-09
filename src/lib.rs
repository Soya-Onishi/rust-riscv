mod core;
mod util;

extern crate goblin;
use goblin::{Object, elf::Elf};

use std::{
    env,
    fs,    
    fmt,
    error,
    collections::HashMap,
};

struct Emulator {
    pub core: core::Core,
    elf_bin: Vec<u8>,
    breakpoints: Vec<u32>,
    labels: HashMap<String, u32>,
}

impl Emulator {
    pub fn new_with_elf_file(filename: String) -> Result<Emulator, String> {
        let binary = fs::read(filename).unwrap();

        Emulator::new_with_binary(binary)
    }

    pub fn new_with_binary(binary: Vec<u8>) -> Result<Emulator, String> {
        let elf = match Object::parse(&binary) {            
            Ok(Object::Elf(elf)) => elf,
            _                    => return Err("not elf binary".to_string()),
        };

        let core = Emulator::make_core(&elf, &binary);
        let labels = match Emulator::get_label(&elf) {
            Ok(labels) => labels,
            Err(e) => return Err(e.to_string()),
        };

        Ok(Emulator {
            core,
            elf_bin: binary,
            breakpoints: Vec::new(),
            labels,
        })
    }

    fn make_core(elf: &Elf, binary: &Vec<u8>) -> core::Core {
        let mut core = core::Core::new(0, true);

        let sections = &elf.section_headers;

        for section in sections.iter() {
            // If the section type is SH_PROGBITS, load it.
            if (section.sh_type & 0x1) > 0 {
                let exec_addr = section.sh_addr as u32;
                let elf_addr = section.sh_offset as usize;
                let section_size = section.sh_size as u32;

                for (index, &bin) in (0..section_size).zip(binary[elf_addr..].iter()) {
                    core.memory.write(exec_addr + index, bin)
                }
            }
        }

        core.pc = elf.entry as u32;

        core
    }

    fn get_label(elf: &Elf) -> Result<HashMap<String, u32>, Box<dyn error::Error>> {
        let hashmap = elf.syms.iter().zip(0..)
            .filter(|(sym, num)| sym.st_shndx != *num)
            .map(|(sym, num)| sym)
            .filter(|sym| sym.st_type() & 4 == 0)
            .map(|sym| {
                let name_result: Result<String, Box<dyn error::Error>> = match elf.strtab.get(sym.st_name) {
                    None => Err(Box::new(ErrorMsg::new("over the strtab region".to_string()))),
                    Some(res) => match res {
                        Ok(name) => Ok(name.to_string()),
                        Err(err) => Err(Box::new(err)),
                    }
                };

                let name = name_result?;
                
                let value = sym.st_value as u32;

                Ok((name, value))
            })
            .collect::<Result<Vec<(String, u32)>, Box<dyn error::Error>>>()?;
            
        Ok(hashmap.into_iter().collect::<HashMap<String, u32>>())
    }

    pub fn run(&mut self) {
        while self.core.is_turnon && !self.is_breakpoint(self.core.pc) {
            self.core.execute();
        }        
    }

    pub fn step(&mut self, num: u32) {
        for _ in 0..num {
            self.core.execute();
        }        
    }

    fn is_breakpoint(&self, pc: u32) -> bool {
        self.breakpoints.contains(&pc)
    }

    pub fn set_breakpoint_with_string(&mut self, label: String) {
        match self.labels.get(&label) {
            Some(&addr) => self.breakpoints.push(addr),
            None => (),
        }
    }

    pub fn set_breakpoint_with_value(&mut self, addr: u32) {
        self.breakpoints.push(addr)
    }
}

#[derive(Debug, Clone)]
struct ErrorMsg {
    msg: String
}

impl ErrorMsg {
    pub fn new(msg: String) -> ErrorMsg {
        ErrorMsg { msg }
    }
}

impl fmt::Display for ErrorMsg {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "ErrorMsg[{}]", &self.msg)
    }
}

impl error::Error for ErrorMsg { }
