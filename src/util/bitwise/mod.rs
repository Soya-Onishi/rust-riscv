pub trait Bitwise {
    fn truncate(&self, upper: usize, lower: usize) -> u32;
    fn get_bit(&self, index: usize) -> u32 { self.truncate(index, index) }
    fn sign_ext(&self, from: usize, to: usize) -> u32;
}

impl Bitwise for u32 {
    fn truncate(&self, upper: usize, lower: usize) -> u32 {
        assert!(upper >= lower);
        assert!(upper < 32);

        let x = -1;
        let mask = !((x as u32) << (upper as u32 - lower as u32));
        (self >> lower) & mask
    }

    fn sign_ext(&self, from: usize, to: usize) -> u32 {
        assert!(from < 32);
        assert!(to < 32);
        assert!(from <= to);

        if ((self >> from) & 1) == 1 {
            let ext_bits = ((-1 << from as u32) ^ ((-1 as i32).checked_shl(to as u32 + 1).unwrap_or(0))) as u32;
            self.to_owned() | ext_bits
        } else {
            self.to_owned()
        }
    }
}

struct Bit {
    value: Vec<u32>,
    length: usize
}

impl Bit {
    fn sign_ext(&self) -> Bit {

    }

    fn bit(&self, index: usize) -> Bit {

    }

    fn truncate(&self, upper: usize, lower: usize) -> Bit {
        fn make_index(n: usize) -> (usize, u32) { (n / 32, (n % 32) as u32) }

        assert!(upper >= lower);
        assert!(upper < self.length);

        let (upper_vec_index, upper_position) = make_index(upper);
        let (lower_vec_index, lower_position) = make_index(lower);

        if upper_vec_index == lower_vec_index {
            let value = self.value[upper_vec_index];
            let mask = !(-1 << (upper as u32 - lower as u32));

            Bit::new_with_length((self >> lower) & mask, upper - lower + 1)
        } else {
            let mut value = Vec::new();
            let lower_value = self.value[lower_vec_index] >> lower_position;
            let mask = !(-1 << (32 - lower_position));
            let last_remain = (&self.value[(lower_vec_index + 1)..(upper_vec_index + 1)]).iter().fold(lower_value, |remain, &elem| {
                let head = (elem & mask) << lower_position;
                value.push(head | remain);
                elem >> lower_position
            });

            let upper_mask = !(-1 << (32 - upper_position));
            let upper_value = self.value[upper_vec_index] & upper_mask;
            let additional_vec =
                if (lower_position + upper_position + 1) < 32 {
                    let value = (upper_value << lower_position) | last_remain;
                    vec![value]
                } else {
                    let first_position = 31 - lower_position;
                    
                };
        }
    }
}

trait BitConstructor<T> {
    fn new(x: T) -> Bit;
    fn new_with_length(x: T, length: usize) -> Bit;
}

impl BitConstructor<u32> for Bit {
    fn new(x: u32) -> Bit {
        Bit {
            value: vec![x],
            length: 32,
        }
    }

    fn new_with_length(x: u32, length: usize) -> Bit {
        let mut at_least: usize = 1;
        for shift_value in 0..31 {
            if ((x >> shift_value) & 1) == 1 {
                at_least = (shift_value + 1) as usize;
            }
        }

        assert!(at_least <= length);
        Bit {
            value: vec![x],
            length,
        }
    }
}

impl BitConstructor<&Vec<u32>> for Bit {
    fn new(value: &Vec<u32>) -> Bit {
        Bit {
            value: value.clone(),
            length: value.len() * 32,
        }
    }

    fn new_with_length(value: &Vec<u32>, length: usize) -> Bit {
        assert!(value.len() > 0);

        let at_least_from_vec = (value.len() - 1) * 32;
        let mut at_least_from_elem = 1;
        let elem = value[0];
        for shift_value in 0..31 {
            if ((elem >> shift_value) & 1) == 1 {
                at_least_from_elem = shift_value + 1;
            }
        }
        assert!(at_least_from_vec + at_least_from_elem as usize <= length);

        Bit { value: value.clone(), length }
    }
}