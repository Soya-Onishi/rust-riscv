pub trait Bitwise: Copy {
    fn truncate(self, upper: Self, lower: Self) -> Self;
    fn extract(self, index: Self) -> Self;
    fn concat(values: &[Self], lengths: &[Self]) -> Self;
    fn sign_ext(self, msb_pos: Self) -> Self;
}

impl Bitwise for u32 {
    fn truncate(self, upper: u32, lower: u32) -> u32 {
        let mask = (1_u64 << (upper as u64 + 1)) - 1;
        let mask = mask as u32;

        (self & mask) >> lower
    }

    fn extract(self, index: u32) -> u32 {
        let mask = std::u32::MAX >> (31 - index);

        (self & mask) >> index
    }

    fn concat(values: &[u32], length: &[u32]) -> u32 {
        let (value, _) = values.iter()
            .zip(length.iter())
            .map(|(&value, &length)| { value & ((1 << length) - 1) })
            .zip(length.iter())
            .fold((0, 0), |(acc, total_len), (value, &length)| {
                (acc | (value << total_len), total_len + length)
            });

        value
    }

    fn sign_ext(self, msb_pos: u32) -> u32 {
        if self & (1 << msb_pos) == 0 { self }
        else { ((std::u32::MAX) ^ ((1 << msb_pos) - 1)) | self }
    }
}

impl Bitwise for u64 {
    fn truncate(self, upper: u64, lower: u64) -> u64 {
        let mask = ((1_u128 << (upper as u128 + 1)) - 1) as u64;

        (self & mask) >> lower
    }

    fn extract(self, index: u64) -> u64 {
        let mask = std::u64::MAX >> (63 - index);

        (self & mask) >> index
    }

    fn concat(values: &[u64], length: &[u64]) -> u64 {
        let (value, _) = values.iter()
            .zip(length.iter())
            .map(|(&value, &length)| { value & ((1 << length) - 1) })
            .zip(length.iter())
            .fold((0, 0), |(acc, total_len), (value, &length)| {
                (acc | (value << total_len), total_len + length)
            });

        value
    }

    fn sign_ext(self, msb_pos: u64) -> u64 {
        if self & (1 << msb_pos) == 0 { self }
        else { ((std::u64::MAX) ^ ((1 << msb_pos) - 1)) | self }
    }
}