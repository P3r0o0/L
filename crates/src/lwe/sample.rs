use crate::lwe::math::{
    add_mod, matrix_add, matrix_vec_mul, mul_mod, sub_mod, vec_add, zeroize_slice, BarrettModulus,
};
use alloc::vec::Vec;

pub type Matrix = Vec<Vec<u64>>;

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct LweSample {
    pub a: Matrix,
    pub b: Vec<u64>,
}

impl LweSample {
    pub fn new(a: Matrix, b: Vec<u64>) -> Self {
        Self { a, b }
    }

    pub fn is_well_formed(&self, m: usize, n: usize, q: u64) -> bool {
        self.a.len() == m
            && self.b.len() == m
            && self
                .a
                .iter()
                .all(|row| row.len() == n && row.iter().all(|&x| x < q))
            && self.b.iter().all(|&x| x < q)
    }

    pub fn to_bytes(&self) -> Vec<u8> {
        let m = self.b.len();
        let n = self.a.first().map(|r| r.len()).unwrap_or(0);
        let mut out = Vec::with_capacity((m * n + m) * 8);
        for row in &self.a {
            for &x in row {
                out.extend_from_slice(&x.to_le_bytes());
            }
        }
        for &x in &self.b {
            out.extend_from_slice(&x.to_le_bytes());
        }
        out
    }

    pub fn from_bytes(bytes: &[u8], m: usize, n: usize, q: u64) -> Option<Self> {
        let total_u64 = m.checked_mul(n)?.checked_add(m)?;
        if bytes.len() != total_u64.checked_mul(8)? {
            return None;
        }
        let mut offset = 0;
        let mut a = Vec::with_capacity(m);
        for _ in 0..m {
            let mut row = Vec::with_capacity(n);
            for _ in 0..n {
                let mut arr = [0u8; 8];
                arr.copy_from_slice(&bytes[offset..offset + 8]);
                offset += 8;
                let val = u64::from_le_bytes(arr);
                if val >= q {
                    return None;
                }
                row.push(val);
            }
            a.push(row);
        }
        let mut b = Vec::with_capacity(m);
        for _ in 0..m {
            let mut arr = [0u8; 8];
            arr.copy_from_slice(&bytes[offset..offset + 8]);
            offset += 8;
            let val = u64::from_le_bytes(arr);
            if val >= q {
                return None;
            }
            b.push(val);
        }
        Some(Self { a, b })
    }

    pub fn add(&self, other: &Self, q: u64) -> Self {
        let a = matrix_add(&self.a, &other.a, q);
        let b = vec_add(&self.b, &other.b, q);
        Self::new(a, b)
    }

    pub fn sub(&self, other: &Self, q: u64) -> Self {
        assert_eq!(self.a.len(), other.a.len());
        assert_eq!(self.b.len(), other.b.len());
        let a: Matrix = self
            .a
            .iter()
            .zip(other.a.iter())
            .map(|(r1, r2)| {
                assert_eq!(r1.len(), r2.len());
                r1.iter()
                    .zip(r2.iter())
                    .map(|(&x, &y)| sub_mod(x, y, q))
                    .collect()
            })
            .collect();
        let b: Vec<u64> = self
            .b
            .iter()
            .zip(other.b.iter())
            .map(|(&x, &y)| sub_mod(x, y, q))
            .collect();
        Self::new(a, b)
    }

    pub fn phase(&self, s: &[u64], q: u64) -> Vec<u64> {
        let as_vec = matrix_vec_mul(&self.a, s, q);
        assert_eq!(self.b.len(), as_vec.len());
        self.b
            .iter()
            .zip(as_vec.iter())
            .map(|(&bi, &asi)| sub_mod(bi, asi, q))
            .collect()
    }

    pub fn encrypt_messages(&self, messages: &[u64], t: u64, q: u64) -> Self {
        assert_eq!(self.b.len(), messages.len());
        assert!(t >= 2 && q > t, "Moduli must satisfy q > t >= 2");
        assert!(
            2u128 * ((q % t) as u128) * ((t - 1) as u128) < (q as u128),
            "Parameters (q={q}, t={t}) violate rounding-decryption margin 2*(q mod t)*(t-1) < q"
        );
        let n = self.a.first().map(|r| r.len()).unwrap_or(0);
        assert!(
            self.is_well_formed(self.b.len(), n, q),
            "Base LWE sample must be well-formed with canonical elements < q"
        );
        let delta = q / t;
        let b = if q < (1u64 << 62) && t < (1u64 << 62) {
            let qb = BarrettModulus::new(q);
            let tb = BarrettModulus::new(t);
            self.b
                .iter()
                .zip(messages.iter())
                .map(|(&bi, &mi)| add_mod(bi, qb.mul_mod(tb.reduce_u64(mi), delta), q))
                .collect()
        } else {
            self.b
                .iter()
                .zip(messages.iter())
                .map(|(&bi, &mi)| add_mod(bi, mul_mod(mi % t, delta, q), q))
                .collect()
        };
        Self::new(self.a.clone(), b)
    }

    pub fn decrypt_messages(&self, s: &[u64], t: u64, q: u64) -> Vec<u64> {
        assert!(t >= 2 && q > t, "Moduli must satisfy q > t >= 2");
        assert!(
            2u128 * ((q % t) as u128) * ((t - 1) as u128) < (q as u128),
            "Parameters (q={q}, t={t}) violate rounding-decryption margin 2*(q mod t)*(t-1) < q"
        );
        let n = self.a.first().map(|r| r.len()).unwrap_or(0);
        assert!(
            self.is_well_formed(self.b.len(), n, q) && s.len() == n && s.iter().all(|&x| x < q),
            "LWE ciphertext and secret key must be well-formed with canonical elements < q"
        );
        let mut v = self.phase(s, q);
        let out = if t == 2 && q < (1u64 << 62) {
            let half_q = q >> 1;
            let two_q = q << 1;
            v.iter()
                .map(|&vi| {
                    let num = (vi << 1) + half_q;
                    ((num >= q) as u64) & ((num < two_q) as u64)
                })
                .collect()
        } else if q < (1u64 << 62)
            && t < (1u64 << 62)
            && ((q - 1) as u128) * (t as u128) + ((q >> 1) as u128) <= (u64::MAX as u128)
        {
            let qb = BarrettModulus::new(q);
            let tb = BarrettModulus::new(t);
            let half_q = q >> 1;
            v.iter()
                .map(|&vi| {
                    let num = vi * t + half_q;
                    let quot = qb.div_rem_u64(num).0;
                    tb.reduce_u64(quot)
                })
                .collect()
        } else {
            let t128 = t as u128;
            let q128 = q as u128;
            v.iter()
                .map(|&vi| ((((vi as u128) * t128 + (q128 >> 1)) / q128) % t128) as u64)
                .collect()
        };
        zeroize_slice(&mut v);
        out
    }
}
