use crate::lwe::sample::Matrix;
use alloc::vec::Vec;
use rand::Rng;

#[inline]
pub fn zeroize_slice(slice: &mut [u64]) {
    for elem in slice.iter_mut() {
        unsafe { core::ptr::write_volatile(elem, 0) };
    }
    core::sync::atomic::compiler_fence(core::sync::atomic::Ordering::SeqCst);
}

#[inline]
pub fn zeroize_i64_slice(slice: &mut [i64]) {
    for elem in slice.iter_mut() {
        unsafe { core::ptr::write_volatile(elem, 0) };
    }
    core::sync::atomic::compiler_fence(core::sync::atomic::Ordering::SeqCst);
}

#[inline]
pub fn zeroize_nested_u64(vecs: &mut [Vec<u64>]) {
    for v in vecs.iter_mut() {
        zeroize_slice(v);
    }
}

#[inline]
pub fn ct_eq_u64(a: u64, b: u64) -> bool {
    let diff = a ^ b;
    ((diff | diff.wrapping_neg()) >> 63) == 0
}

#[inline]
pub fn ct_eq_slice(a: &[u64], b: &[u64]) -> bool {
    if a.len() != b.len() {
        return false;
    }
    let mut acc = 0u64;
    for (&x, &y) in a.iter().zip(b.iter()) {
        acc |= x ^ y;
    }
    ct_eq_u64(acc, 0)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct BarrettModulus {
    pub q: u64,
    pub mu: u64,
    pub k: u32,
    pub mu_2k: u64,
}

impl BarrettModulus {
    pub fn new(q: u64) -> Self {
        assert!(
            q >= 2 && q < (1u64 << 62),
            "Modulus q must satisfy 2 <= q < 2^62"
        );
        let mu = ((1u128 << 64) / (q as u128)) as u64;
        let k = (64 - q.leading_zeros()).clamp(2, 62);
        let mu_2k = ((1u128 << (2 * k)) / (q as u128)) as u64;
        Self { q, mu, k, mu_2k }
    }

    #[inline]
    pub fn reduce_u64(&self, x: u64) -> u64 {
        self.div_rem_u64(x).1
    }

    #[inline]
    pub fn div_rem_u64(&self, x: u64) -> (u64, u64) {
        let q_est = (((x as u128) * (self.mu as u128)) >> 64) as u64;
        let r = x.wrapping_sub(q_est.wrapping_mul(self.q));
        let ge = (r >= self.q) as u64;
        let ge_mask = 0u64.wrapping_sub(ge);
        (q_est.wrapping_add(ge), r.wrapping_sub(self.q & ge_mask))
    }

    #[inline]
    pub fn mul_mod(&self, a: u64, b: u64) -> u64 {
        let a_red = self.reduce_u64(a);
        let b_red = self.reduce_u64(b);
        let x = (a_red as u128) * (b_red as u128);
        let x_hi = (x >> (self.k - 1)) as u64;
        let q_est = ((x_hi as u128) * (self.mu_2k as u128)) >> (self.k + 1);
        let r = (x.wrapping_sub(q_est.wrapping_mul(self.q as u128))) as u64;
        let ge1 = 0u64.wrapping_sub((r >= self.q) as u64);
        let r = r.wrapping_sub(self.q & ge1);
        let ge2 = 0u64.wrapping_sub((r >= self.q) as u64);
        r.wrapping_sub(self.q & ge2)
    }
}

#[inline]
pub fn add_mod(a: u64, b: u64, q: u64) -> u64 {
    let sum = a as u128 + b as u128;
    let q128 = q as u128;
    let ge_mask = 0u128.wrapping_sub((sum >= q128) as u128);
    (sum.wrapping_sub(q128 & ge_mask)) as u64
}

#[inline]
pub fn sub_mod(a: u64, b: u64, q: u64) -> u64 {
    let diff = a.wrapping_sub(b);
    let lt_mask = 0u64.wrapping_sub((a < b) as u64);
    diff.wrapping_add(q & lt_mask)
}

#[inline]
pub fn mul_mod(a: u64, b: u64, q: u64) -> u64 {
    ((a as u128 * b as u128) % (q as u128)) as u64
}

pub fn matrix_vec_mul(a: &Matrix, s: &[u64], q: u64) -> Vec<u64> {
    if a.is_empty() {
        return Vec::new();
    }
    let mut result = Vec::with_capacity(a.len());
    for row in a {
        assert_eq!(row.len(), s.len());
        let mut sum = 0u64;
        for (&a_ij, &s_j) in row.iter().zip(s.iter()) {
            sum = add_mod(sum, mul_mod(a_ij, s_j, q), q);
        }
        result.push(sum);
    }
    result
}

pub fn vec_add(v1: &[u64], v2: &[u64], q: u64) -> Vec<u64> {
    assert_eq!(v1.len(), v2.len());
    v1.iter()
        .zip(v2.iter())
        .map(|(&x, &y)| add_mod(x, y, q))
        .collect()
}

pub fn matrix_add(m1: &Matrix, m2: &Matrix, q: u64) -> Matrix {
    assert_eq!(m1.len(), m2.len());
    m1.iter()
        .zip(m2.iter())
        .map(|(row1, row2)| vec_add(row1, row2, q))
        .collect()
}

#[inline]
pub fn centered_lift(x: u64, q: u64) -> i64 {
    let half_q = q >> 1;
    let gt_mask = 0i64.wrapping_sub((x > half_q) as i64);
    let pos = x as i64;
    let neg = -((q.wrapping_sub(x)) as i64);
    (neg & gt_mask) | (pos & !gt_mask)
}

#[inline]
pub fn norm(x: u64, q: u64) -> u64 {
    let half_q = q >> 1;
    let gt_mask = 0u64.wrapping_sub((x > half_q) as u64);
    let reflected = q.wrapping_sub(x);
    (reflected & gt_mask) | (x & !gt_mask)
}

pub fn norm_inf(v: &[u64], q: u64) -> u64 {
    v.iter().map(|&x| norm(x, q)).max().unwrap_or(0)
}

#[inline]
pub fn compress_coeff(x: u64, q: u64, d: u32) -> u64 {
    assert!(
        d > 0 && d < 64 && q >= 2,
        "Invalid compression bit-width d or modulus q"
    );
    let val = (if x < q { x } else { x % q }) as u128;
    let q128 = q as u128;
    let mask = (1u128 << d) - 1;
    (((val << d) + (q128 >> 1)) / q128 & mask) as u64
}

#[inline]
pub fn decompress_coeff(y: u64, q: u64, d: u32) -> u64 {
    assert!(
        d > 0 && d < 64 && q >= 2,
        "Invalid compression bit-width d or modulus q"
    );
    let mask = (1u64 << d) - 1;
    let y_masked = (y & mask) as u128;
    let q128 = q as u128;
    let half = 1u128 << (d - 1);
    (((y_masked * q128) + half) >> d) as u64
}

#[inline]
pub fn sample_ternary_mod_q<R: Rng + ?Sized>(rng: &mut R, q: u64) -> u64 {
    let x = rng.next_u64();
    let q3 = (((x as u128) * 0xAAAA_AAAA_AAAA_AAABu128) >> 65) as u64;
    let rem = x.wrapping_sub(q3.wrapping_mul(3));
    let is_one = 0u64.wrapping_sub((rem == 1) as u64);
    let is_two = 0u64.wrapping_sub((rem == 2) as u64);
    (1u64 & is_one) | (q.wrapping_sub(1) & is_two)
}

#[inline]
pub fn sample_ternary_i64<R: Rng + ?Sized>(rng: &mut R) -> i64 {
    let x = rng.next_u64();
    let q3 = (((x as u128) * 0xAAAA_AAAA_AAAA_AAABu128) >> 65) as u64;
    let rem = x.wrapping_sub(q3.wrapping_mul(3));
    let is_one = (rem == 1) as i64;
    let is_two = (rem == 2) as i64;
    is_one - is_two
}

#[inline]
pub fn is_gadget_covering(base: u64, digits: usize, modulus: u64) -> bool {
    if base < 2 || digits == 0 {
        return false;
    }
    let mut acc: u128 = 1;
    let b128 = base as u128;
    let m128 = modulus as u128;
    for _ in 0..digits {
        acc = acc.saturating_mul(b128);
        if acc >= m128 {
            return true;
        }
    }
    acc >= m128
}

pub fn is_prime_u64(n: u64) -> bool {
    if n < 2 {
        return false;
    }
    for &p in &[2u64, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37] {
        if n == p {
            return true;
        }
        if n % p == 0 {
            return false;
        }
    }
    let mut d = n - 1;
    let s = d.trailing_zeros();
    d >>= s;

    const BASES: [u64; 7] = [2, 325, 9375, 28178, 450775, 9780504, 1795265022];

    if n < (1u64 << 62) {
        let b = BarrettModulus::new(n);
        for &a in &BASES {
            let a_mod = b.reduce_u64(a);
            if a_mod == 0 {
                continue;
            }
            let mut x = pow_mod_barrett_u64(a_mod, d, &b);
            if x == 1 || x == n - 1 {
                continue;
            }
            let mut composite = true;
            for _ in 1..s {
                x = b.mul_mod(x, x);
                if x == n - 1 {
                    composite = false;
                    break;
                }
            }
            if composite {
                return false;
            }
        }
    } else {
        for &a in &BASES {
            let a_mod = a % n;
            if a_mod == 0 {
                continue;
            }
            let mut x = pow_mod_u128_fallback(a_mod, d, n);
            if x == 1 || x == n - 1 {
                continue;
            }
            let mut composite = true;
            for _ in 1..s {
                x = mul_mod(x, x, n);
                if x == n - 1 {
                    composite = false;
                    break;
                }
            }
            if composite {
                return false;
            }
        }
    }
    true
}

fn pow_mod_barrett_u64(mut base: u64, mut exp: u64, b: &BarrettModulus) -> u64 {
    let mut res = 1u64;
    while exp > 0 {
        if (exp & 1) == 1 {
            res = b.mul_mod(res, base);
        }
        base = b.mul_mod(base, base);
        exp >>= 1;
    }
    res
}

fn pow_mod_u128_fallback(mut base: u64, mut exp: u64, n: u64) -> u64 {
    let mut res = 1u64;
    base %= n;
    while exp > 0 {
        if (exp & 1) == 1 {
            res = mul_mod(res, base, n);
        }
        base = mul_mod(base, base, n);
        exp >>= 1;
    }
    res
}
