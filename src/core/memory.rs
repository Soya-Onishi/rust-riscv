extern crate paste;

use std::collections::HashMap;
use crate::util::exception::Exception;

macro_rules! make_interface {
    ($( { $tpe: tt, $size: literal } )*) => {
        paste::item! {$(
            fn [<read_ $tpe _impl>](&self, address: u32) -> Result<$tpe, Exception>{
                if address % $size != 0 { return Err(Exception::LoadAddressMisaligned(address)) }

                let result = (0..$size).fold(0, |acc, offset| {
                    let data = self.read(address + (offset as u32)) as $tpe;
                    acc | (data << (offset * 8))
                });

                Ok(result)
            }

            fn [<write_ $tpe _impl>](&mut self, address: u32, value: $tpe) -> Result<(), Exception> {
                if address % $size != 0 { return Err(Exception::StoreAddressMisaligned(address)) }

                (0..$size).for_each(|offset| {
                    let stored_data = (value >> (offset * 8)) as u8;
                    self.write(address + (offset as u32), stored_data);
                });

                Ok(())
            }
        )*}
    }
}

pub struct MMU {
    mem: HashMap<usize, [u8; 2048]>,
    register_reserved_addr: Option<u32>,
}

impl MMU {
    pub fn new() -> MMU {
        MMU {
            mem: HashMap::new(),
            register_reserved_addr: None,
        }
    }

    make_interface!(
        {  u8, 1 }
        { u16, 2 }
        { u32, 4 }
    );

    pub fn  read_u8(&self, address: u32) -> Result< u8, Exception> { self.read_u8_impl(address) }
    pub fn read_u16(&self, address: u32) -> Result<u16, Exception> { self.read_u16_impl(address) }
    pub fn read_u32(&self, address: u32) -> Result<u32, Exception> { self.read_u32_impl(address) }

    pub fn  write_u8(&mut self, address: u32, value:  u8) -> Result<(), Exception>{ self.write_u8_impl(address, value) }
    pub fn write_u16(&mut self, address: u32, value: u16) -> Result<(), Exception> { self.write_u16_impl(address, value) }
    pub fn write_u32(&mut self, address: u32, value: u32) -> Result<(), Exception> { self.write_u32_impl(address, value) }

    fn read(&self, address: u32) -> u8 {
        let (offset, index) = separate_addr(address);

        match self.mem.get(&offset) {
            Some(table) => table[index],
            None => 0
        }
    }

    fn write(&mut self, address: u32, value: u8) {
        let (offset, index) = separate_addr(address);
        match self.mem.get_mut(&offset) {
            Some(table) => table[index] = value,
            None => {
                let mut table = [0_u8; 2048];
                table[index] = value;
                self.mem.insert(offset, table);
            }
        }
    }

    pub fn set_reservation(&mut self, addr: u32) {
        self.register_reserved_addr = Some(addr);
    }

    pub fn yield_reservation(&mut self) {
        self.register_reserved_addr = None;
    }

    pub fn check_reservation(&self, addr: u32) -> bool {
        match self.register_reserved_addr {
            Some(reserved) => reserved == addr,
            None                 => false,
        }
    }
}

fn separate_addr(address: u32) -> (usize, usize) {
    let offset = address >> 11;
    let index = address & ((1 << 11) - 1);

    (offset as usize, index as usize)
}