use alloc::vec::Vec;

pub fn packed_byte_len(n: usize, d: u32) -> Option<usize> {
    if d == 0 || d > 62 {
        return None;
    }
    let total_bits = n.checked_mul(d as usize)?;
    Some(total_bits.checked_add(7)? / 8)
}

pub fn pack_bits(coeffs: &[u64], d: u32) -> Vec<u8> {
    assert!(d > 0 && d <= 62, "bit width d must be in 1..=62");
    let bound = 1u64 << d;
    let byte_len = packed_byte_len(coeffs.len(), d).expect("packed_byte_len overflow");
    let mut out = Vec::with_capacity(byte_len);
    let mut acc: u128 = 0;
    let mut acc_bits: u32 = 0;

    for &c in coeffs {
        assert!(c < bound, "coefficient exceeds 2^d bound");
        acc |= (c as u128) << acc_bits;
        acc_bits += d;
        while acc_bits >= 8 {
            out.push((acc & 0xFF) as u8);
            acc >>= 8;
            acc_bits -= 8;
        }
    }

    if acc_bits > 0 {
        out.push((acc & 0xFF) as u8);
    }

    out
}

pub fn unpack_bits(bytes: &[u8], n: usize, d: u32) -> Option<Vec<u64>> {
    if d == 0 || d > 62 {
        return None;
    }
    unpack_bits_bounded(bytes, n, d, 1u64 << d)
}

pub fn unpack_bits_bounded(bytes: &[u8], n: usize, d: u32, bound: u64) -> Option<Vec<u64>> {
    let expected_len = packed_byte_len(n, d)?;
    if bytes.len() != expected_len || bound == 0 || bound > (1u64 << d) {
        return None;
    }

    let mask: u128 = (1u128 << d) - 1;
    let mut out = Vec::with_capacity(n);
    let mut acc: u128 = 0;
    let mut acc_bits: u32 = 0;
    let mut byte_idx = 0;

    for _ in 0..n {
        while acc_bits < d {
            acc |= (bytes[byte_idx] as u128) << acc_bits;
            acc_bits += 8;
            byte_idx += 1;
        }
        let val = (acc & mask) as u64;
        if val >= bound {
            return None;
        }
        out.push(val);
        acc >>= d;
        acc_bits -= d;
    }

    if byte_idx != bytes.len() || acc != 0 {
        return None;
    }

    Some(out)
}
