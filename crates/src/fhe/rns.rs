use crate::lwe::math::{add_mod, sub_mod, BarrettModulus};
use crate::lwe::ntt::{inv_mod, NTTTable};
use crate::lwe::pke::ModPKEParams;
use crate::lwe::poly::Polynomial;
use alloc::vec;
use alloc::vec::Vec;
use core::cmp::Ordering;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct BigUint {
    pub limbs: Vec<u64>,
}

impl BigUint {
    pub fn zero() -> Self {
        Self { limbs: Vec::new() }
    }

    pub fn from_u64(v: u64) -> Self {
        if v == 0 {
            Self::zero()
        } else {
            Self { limbs: vec![v] }
        }
    }

    pub fn is_zero(&self) -> bool {
        self.limbs.is_empty()
    }

    fn normalize(&mut self) {
        while self.limbs.last() == Some(&0) {
            self.limbs.pop();
        }
    }

    pub fn cmp(&self, other: &Self) -> Ordering {
        match self.limbs.len().cmp(&other.limbs.len()) {
            Ordering::Equal => {
                for (&a, &b) in self.limbs.iter().rev().zip(other.limbs.iter().rev()) {
                    match a.cmp(&b) {
                        Ordering::Equal => continue,
                        ord => return ord,
                    }
                }
                Ordering::Equal
            }
            ord => ord,
        }
    }

    pub fn add(&self, other: &Self) -> Self {
        let max_len = self.limbs.len().max(other.limbs.len());
        let mut out = Vec::with_capacity(max_len + 1);
        let mut carry = 0u128;
        for i in 0..max_len {
            let a = self.limbs.get(i).copied().unwrap_or(0) as u128;
            let b = other.limbs.get(i).copied().unwrap_or(0) as u128;
            let sum = a + b + carry;
            out.push(sum as u64);
            carry = sum >> 64;
        }
        if carry > 0 {
            out.push(carry as u64);
        }
        let mut res = Self { limbs: out };
        res.normalize();
        res
    }

    pub fn sub(&self, other: &Self) -> Self {
        assert!(self.cmp(other) != Ordering::Less, "BigUint::sub underflow");
        let mut out = Vec::with_capacity(self.limbs.len());
        let mut borrow = 0i128;
        for i in 0..self.limbs.len() {
            let a = self.limbs[i] as i128;
            let b = other.limbs.get(i).copied().unwrap_or(0) as i128;
            let diff = a - b - borrow;
            if diff < 0 {
                out.push((diff + (1i128 << 64)) as u64);
                borrow = 1;
            } else {
                out.push(diff as u64);
                borrow = 0;
            }
        }
        let mut res = Self { limbs: out };
        res.normalize();
        res
    }

    pub fn mul_u64(&self, rhs: u64) -> Self {
        if self.is_zero() || rhs == 0 {
            return Self::zero();
        }
        let mut out = Vec::with_capacity(self.limbs.len() + 1);
        let mut carry = 0u128;
        let m = rhs as u128;
        for &limb in &self.limbs {
            let prod = (limb as u128) * m + carry;
            out.push(prod as u64);
            carry = prod >> 64;
        }
        if carry > 0 {
            out.push(carry as u64);
        }
        let mut res = Self { limbs: out };
        res.normalize();
        res
    }

    pub fn div_rem_u64(&self, rhs: u64) -> (Self, u64) {
        assert!(rhs > 0, "division by zero");
        if self.is_zero() {
            return (Self::zero(), 0);
        }
        let mut quot = vec![0u64; self.limbs.len()];
        let mut rem = 0u128;
        let d = rhs as u128;
        for i in (0..self.limbs.len()).rev() {
            let cur = (rem << 64) | (self.limbs[i] as u128);
            quot[i] = (cur / d) as u64;
            rem = cur % d;
        }
        let mut q_big = Self { limbs: quot };
        q_big.normalize();
        (q_big, rem as u64)
    }

    pub fn rem_u64(&self, rhs: u64) -> u64 {
        self.div_rem_u64(rhs).1
    }

    pub fn shr1(&self) -> Self {
        if self.is_zero() {
            return Self::zero();
        }
        let mut out = vec![0u64; self.limbs.len()];
        let mut carry = 0u64;
        for i in (0..self.limbs.len()).rev() {
            let next_carry = self.limbs[i] << 63;
            out[i] = (self.limbs[i] >> 1) | carry;
            carry = next_carry;
        }
        let mut res = Self { limbs: out };
        res.normalize();
        res
    }

    pub fn rem_big(&self, modulus: &Self) -> Self {
        self.div_rem_big(modulus).1
    }

    pub fn div_rem_big(&self, divisor: &Self) -> (Self, Self) {
        assert!(!divisor.is_zero(), "BigUint division by zero");
        if self.cmp(divisor) == Ordering::Less {
            return (Self::zero(), self.clone());
        }
        let bit_len = self.bit_len();
        let mut quot = Self::zero();
        let mut rem = Self::zero();
        for bit_idx in (0..bit_len).rev() {
            rem = rem.mul_u64(2);
            if self.get_bit(bit_idx) {
                rem = rem.add(&Self::from_u64(1));
            }
            if rem.cmp(divisor) != Ordering::Less {
                rem = rem.sub(divisor);
                quot.set_bit(bit_idx);
            }
        }
        quot.normalize();
        rem.normalize();
        (quot, rem)
    }

    pub fn bit_len(&self) -> usize {
        if let Some(&top) = self.limbs.last() {
            (self.limbs.len() - 1) * 64 + (64 - top.leading_zeros() as usize)
        } else {
            0
        }
    }

    pub fn get_bit(&self, bit_idx: usize) -> bool {
        let limb_idx = bit_idx / 64;
        let bit_off = bit_idx % 64;
        if let Some(&limb) = self.limbs.get(limb_idx) {
            ((limb >> bit_off) & 1) != 0
        } else {
            false
        }
    }

    pub fn set_bit(&mut self, bit_idx: usize) {
        let limb_idx = bit_idx / 64;
        let bit_off = bit_idx % 64;
        if self.limbs.len() <= limb_idx {
            self.limbs.resize(limb_idx + 1, 0);
        }
        self.limbs[limb_idx] |= 1u64 << bit_off;
    }

    pub fn to_f64_log2(&self) -> f64 {
        let bits = self.bit_len();
        if bits == 0 {
            return 0.0;
        }
        let top = *self.limbs.last().unwrap() as f64;
        let top_bits = 64 - self.limbs.last().unwrap().leading_zeros();
        let mantissa = top / ((1u64 << (top_bits - 1)) as f64);
        ((bits - 1) as f64) + crate::fhe::rns::approx_log2_1_to_2(mantissa)
    }
}

pub fn approx_log2_1_to_2(x: f64) -> f64 {
    let y = (x - 1.0) / (x + 1.0);
    let y2 = y * y;
    let mut term = y;
    let mut sum = 0.0;
    for k in 0..8 {
        sum += term / ((2 * k + 1) as f64);
        term *= y2;
    }
    2.0 * sum / core::f64::consts::LN_2
}

pub fn gcd_u64(mut a: u64, mut b: u64) -> u64 {
    while b != 0 {
        let r = a % b;
        a = b;
        b = r;
    }
    a
}

#[derive(Clone, Debug)]
pub struct RnsBasis {
    pub n: usize,
    pub moduli: Vec<u64>,
    pub psi: Vec<u64>,
    pub tables: Vec<NTTTable>,
    pub barretts: Vec<BarrettModulus>,
    pub big_q: BigUint,
    pub q_hat: Vec<BigUint>,
    pub q_hat_inv_mod_qi: Vec<u64>,
    pub gadget_residues: Vec<Vec<u64>>,
}

impl RnsBasis {
    pub fn new(n: usize, moduli: Vec<u64>) -> Self {
        assert!(
            n > 0 && n.is_power_of_two(),
            "RNS degree n must be a power of two"
        );
        assert!(!moduli.is_empty(), "RNS basis must have at least one limb");

        for i in 0..moduli.len() {
            let qi = moduli[i];
            assert!(
                qi > 2 && qi < (1u64 << 62),
                "RNS modulus must be in (2, 2^62)"
            );
            assert!(is_prime_u64(qi), "Each RNS modulus q_i must be prime");
            assert_eq!(
                (qi - 1) % (2 * (n as u64)),
                0,
                "Each RNS modulus q_i must satisfy q_i == 1 mod 2N"
            );
            for j in (i + 1)..moduli.len() {
                assert_eq!(
                    gcd_u64(qi, moduli[j]),
                    1,
                    "RNS moduli must be pairwise coprime"
                );
            }
        }

        let mut psi = Vec::with_capacity(moduli.len());
        let mut tables = Vec::with_capacity(moduli.len());
        let mut barretts = Vec::with_capacity(moduli.len());
        let mut big_q = BigUint::from_u64(1);

        for &qi in &moduli {
            let psi_i = ModPKEParams::find_psi(n, qi);
            psi.push(psi_i);
            tables.push(NTTTable::new(n, psi_i, qi));
            barretts.push(BarrettModulus::new(qi));
            big_q = big_q.mul_u64(qi);
        }

        let l = moduli.len();
        let mut q_hat = Vec::with_capacity(l);
        let mut q_hat_inv_mod_qi = Vec::with_capacity(l);

        for i in 0..l {
            let qi = moduli[i];
            let (qh, rem) = big_q.div_rem_u64(qi);
            debug_assert_eq!(rem, 0);
            let qh_mod_qi = qh.rem_u64(qi);
            let inv = inv_mod(qh_mod_qi, qi);
            q_hat.push(qh);
            q_hat_inv_mod_qi.push(inv);
        }

        let mut gadget_residues = Vec::with_capacity(l);
        for i in 0..l {
            let g_big = q_hat[i].mul_u64(q_hat_inv_mod_qi[i]);
            let mut row = Vec::with_capacity(l);
            for j in 0..l {
                row.push(g_big.rem_u64(moduli[j]));
            }
            gadget_residues.push(row);
        }

        Self {
            n,
            moduli,
            psi,
            tables,
            barretts,
            big_q,
            q_hat,
            q_hat_inv_mod_qi,
            gadget_residues,
        }
    }

    pub fn num_limbs(&self) -> usize {
        self.moduli.len()
    }

    pub fn log2_q(&self) -> f64 {
        self.big_q.to_f64_log2()
    }

    pub fn drop_last_limb(&self) -> Self {
        assert!(
            self.moduli.len() > 1,
            "Cannot drop last limb when only 1 limb remains"
        );
        let new_moduli = self.moduli[..self.moduli.len() - 1].to_vec();
        Self::new(self.n, new_moduli)
    }

    pub fn crt_reconstruct_coeff(&self, residues: &[u64]) -> BigUint {
        assert_eq!(residues.len(), self.moduli.len());
        let mut sum = BigUint::zero();
        for (i, &ri) in residues.iter().enumerate() {
            let qi = self.moduli[i];
            let yi = self.barretts[i].mul_mod(ri % qi, self.q_hat_inv_mod_qi[i]);
            let term = self.q_hat[i].mul_u64(yi);
            sum = sum.add(&term);
        }
        sum.rem_big(&self.big_q)
    }

    pub fn crt_reconstruct_centered_magnitude_and_sign(&self, residues: &[u64]) -> (BigUint, bool) {
        let x = self.crt_reconstruct_coeff(residues);
        let half_q = self.big_q.shr1();
        if x.cmp(&half_q) == Ordering::Greater {
            (self.big_q.sub(&x), true)
        } else {
            (x, false)
        }
    }

    pub fn fast_bconv_coeff(&self, residues: &[u64], target_moduli: &[u64]) -> Vec<u64> {
        assert_eq!(residues.len(), self.moduli.len());
        let l = self.moduli.len();
        let mut y = Vec::with_capacity(l);
        for i in 0..l {
            let qi = self.moduli[i];
            y.push(self.barretts[i].mul_mod(residues[i] % qi, self.q_hat_inv_mod_qi[i]));
        }

        let mut out = Vec::with_capacity(target_moduli.len());
        for &pj in target_moduli {
            let bp = BarrettModulus::new(pj);
            let mut acc = 0u64;
            for i in 0..l {
                let qh_mod_pj = self.q_hat[i].rem_u64(pj);
                let prod = bp.mul_mod(y[i] % pj, qh_mod_pj);
                acc = add_mod(acc, prod, pj);
            }
            out.push(acc);
        }
        out
    }

    pub fn bconv_exact_coeff(&self, residues: &[u64], target_moduli: &[u64]) -> Vec<u64> {
        assert_eq!(residues.len(), self.moduli.len());
        let x_big = self.crt_reconstruct_coeff(residues);
        target_moduli.iter().map(|&pj| x_big.rem_u64(pj)).collect()
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RnsPoly {
    pub limbs: Vec<Polynomial>,
}

impl RnsPoly {
    pub fn zero(basis: &RnsBasis) -> Self {
        let limbs = (0..basis.num_limbs())
            .map(|_| Polynomial::zero(basis.n))
            .collect();
        Self { limbs }
    }

    pub fn from_single_poly(poly: &Polynomial, basis: &RnsBasis) -> Self {
        assert_eq!(poly.coeffs.len(), basis.n);
        let limbs = basis
            .moduli
            .iter()
            .map(|&qi| Polynomial::new(poly.coeffs.iter().map(|&c| c % qi).collect()))
            .collect();
        Self { limbs }
    }

    pub fn from_signed_i64(coeffs: &[i64], basis: &RnsBasis) -> Self {
        assert_eq!(coeffs.len(), basis.n);
        let limbs = basis
            .moduli
            .iter()
            .zip(basis.barretts.iter())
            .map(|(&qi, barrett)| {
                let c_vec = coeffs
                    .iter()
                    .map(|&v| {
                        let is_neg = (v < 0) as u64;
                        let neg_mask = 0u64.wrapping_sub(is_neg);
                        let abs_mod = barrett.reduce_u64(v.unsigned_abs());
                        let nz_mask = 0u64.wrapping_sub((abs_mod != 0) as u64);
                        let neg_val = qi.wrapping_sub(abs_mod) & nz_mask;
                        (neg_val & neg_mask) | (abs_mod & !neg_mask)
                    })
                    .collect();
                Polynomial::new(c_vec)
            })
            .collect();
        Self { limbs }
    }

    pub fn is_well_formed(&self, basis: &RnsBasis) -> bool {
        self.limbs.len() == basis.num_limbs()
            && self
                .limbs
                .iter()
                .zip(basis.moduli.iter())
                .all(|(p, &qi)| p.coeffs.len() == basis.n && p.is_canonical(qi))
    }

    pub fn add(&self, other: &Self, basis: &RnsBasis) -> Self {
        assert_eq!(self.limbs.len(), basis.num_limbs());
        assert_eq!(other.limbs.len(), basis.num_limbs());
        let limbs = (0..basis.num_limbs())
            .map(|i| self.limbs[i].add(&other.limbs[i], basis.moduli[i]))
            .collect();
        Self { limbs }
    }

    pub fn sub(&self, other: &Self, basis: &RnsBasis) -> Self {
        assert_eq!(self.limbs.len(), basis.num_limbs());
        assert_eq!(other.limbs.len(), basis.num_limbs());
        let limbs = (0..basis.num_limbs())
            .map(|i| self.limbs[i].sub(&other.limbs[i], basis.moduli[i]))
            .collect();
        Self { limbs }
    }

    pub fn neg(&self, basis: &RnsBasis) -> Self {
        Self::zero(basis).sub(self, basis)
    }

    pub fn mul_ntt(&self, other: &Self, basis: &RnsBasis) -> Self {
        assert_eq!(self.limbs.len(), basis.num_limbs());
        assert_eq!(other.limbs.len(), basis.num_limbs());
        let limbs = (0..basis.num_limbs())
            .map(|i| basis.tables[i].mul_ntt(&self.limbs[i], &other.limbs[i]))
            .collect();
        Self { limbs }
    }

    pub fn scalar_mul_limbs(&self, scalars: &[u64], basis: &RnsBasis) -> Self {
        assert_eq!(self.limbs.len(), basis.num_limbs());
        assert_eq!(scalars.len(), basis.num_limbs());
        let limbs = (0..basis.num_limbs())
            .map(|i| {
                let s = scalars[i] % basis.moduli[i];
                let b = &basis.barretts[i];
                Polynomial::new(
                    self.limbs[i]
                        .coeffs
                        .iter()
                        .map(|&c| b.mul_mod(c, s))
                        .collect(),
                )
            })
            .collect();
        Self { limbs }
    }

    pub fn apply_galois(&self, g: usize, basis: &RnsBasis) -> Self {
        let limbs = (0..basis.num_limbs())
            .map(|i| self.limbs[i].apply_galois(g, basis.moduli[i]))
            .collect();
        Self { limbs }
    }

    pub fn gadget_decompose(&self, basis: &RnsBasis) -> Vec<RnsPoly> {
        let l = basis.num_limbs();
        let mut digits = Vec::with_capacity(l);
        for i in 0..l {
            digits.push(Self::from_single_poly(&self.limbs[i], basis));
        }
        digits
    }

    pub fn coeff_residues(&self, coeff_idx: usize) -> Vec<u64> {
        self.limbs.iter().map(|p| p.coeffs[coeff_idx]).collect()
    }

    pub fn norm_inf_big(&self, basis: &RnsBasis) -> BigUint {
        let mut max_norm = BigUint::zero();
        for k in 0..basis.n {
            let residues = self.coeff_residues(k);
            let (mag, _) = basis.crt_reconstruct_centered_magnitude_and_sign(&residues);
            if mag.cmp(&max_norm) == Ordering::Greater {
                max_norm = mag;
            }
        }
        max_norm
    }

    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::new();
        out.extend_from_slice(&(self.limbs.len() as u64).to_le_bytes());
        for p in &self.limbs {
            out.extend_from_slice(&p.to_bytes());
        }
        out
    }

    pub fn from_bytes(bytes: &[u8], basis: &RnsBasis) -> Option<Self> {
        if bytes.len() < 8 {
            return None;
        }
        let mut arr8 = [0u8; 8];
        arr8.copy_from_slice(&bytes[0..8]);
        let l = u64::from_le_bytes(arr8) as usize;
        if l != basis.num_limbs() {
            return None;
        }
        let poly_bytes = basis.n.checked_mul(8)?;
        let expected = 8usize.checked_add(l.checked_mul(poly_bytes)?)?;
        if bytes.len() != expected {
            return None;
        }
        let mut offset = 8;
        let mut limbs = Vec::with_capacity(l);
        for i in 0..l {
            let p = Polynomial::from_bytes(
                &bytes[offset..offset + poly_bytes],
                basis.n,
                basis.moduli[i],
            )?;
            offset += poly_bytes;
            limbs.push(p);
        }
        Some(Self { limbs })
    }

    pub fn zeroize(&mut self) {
        for p in self.limbs.iter_mut() {
            p.zeroize();
        }
    }
}

pub fn scale_mod_switch_drop_last_limb(poly: &RnsPoly, basis: &RnsBasis) -> RnsPoly {
    let l = basis.num_limbs();
    assert!(l > 1, "Must have at least 2 limbs to drop a limb");
    let ql = basis.moduli[l - 1];
    let half_ql = ql / 2;
    let last_limb = &poly.limbs[l - 1];
    let mut new_limbs = Vec::with_capacity(l - 1);

    for i in 0..(l - 1) {
        let qi = basis.moduli[i];
        let ql_inv = inv_mod(ql % qi, qi);
        let b_i = &basis.barretts[i];
        let mut coeffs = Vec::with_capacity(basis.n);
        for k in 0..basis.n {
            let xl_shifted = (last_limb.coeffs[k] + half_ql) % ql;
            let delta_i = if xl_shifted >= half_ql {
                (xl_shifted - half_ql) % qi
            } else {
                let neg = (half_ql - xl_shifted) % qi;
                if neg == 0 {
                    0
                } else {
                    qi - neg
                }
            };
            let diff = sub_mod(poly.limbs[i].coeffs[k], delta_i, qi);
            coeffs.push(b_i.mul_mod(diff, ql_inv));
        }
        new_limbs.push(Polynomial::new(coeffs));
    }

    RnsPoly { limbs: new_limbs }
}

pub fn scale_bgv_drop_last_limb(poly: &RnsPoly, basis: &RnsBasis, t: u64) -> RnsPoly {
    let l = basis.num_limbs();
    assert!(l > 1, "Must have at least 2 limbs to drop a limb");
    let ql = basis.moduli[l - 1];
    let half_ql = ql / 2;
    let t_inv_mod_ql = inv_mod(t % ql, ql);
    let b_l = &basis.barretts[l - 1];
    let last_limb = &poly.limbs[l - 1];

    let mut delta_signed = Vec::with_capacity(basis.n);
    for k in 0..basis.n {
        let neg_c = if last_limb.coeffs[k] == 0 {
            0
        } else {
            ql - last_limb.coeffs[k]
        };
        let d_mod_ql = b_l.mul_mod(neg_c, t_inv_mod_ql);
        if d_mod_ql <= half_ql {
            delta_signed.push(d_mod_ql as i64);
        } else {
            delta_signed.push(-((ql - d_mod_ql) as i64));
        }
    }

    let mut new_limbs = Vec::with_capacity(l - 1);
    for i in 0..(l - 1) {
        let qi = basis.moduli[i];
        let ql_inv = inv_mod(ql % qi, qi);
        let b_i = &basis.barretts[i];
        let t_mod_qi = t % qi;
        let mut coeffs = Vec::with_capacity(basis.n);
        for k in 0..basis.n {
            let d = delta_signed[k];
            let t_delta_mod_qi = if d >= 0 {
                b_i.mul_mod((d as u64) % qi, t_mod_qi)
            } else {
                let mag = b_i.mul_mod((d.unsigned_abs()) % qi, t_mod_qi);
                if mag == 0 {
                    0
                } else {
                    qi - mag
                }
            };
            let adjusted = add_mod(poly.limbs[i].coeffs[k], t_delta_mod_qi, qi);
            coeffs.push(b_i.mul_mod(adjusted, ql_inv));
        }
        new_limbs.push(Polynomial::new(coeffs));
    }

    RnsPoly { limbs: new_limbs }
}

pub fn generate_aux_basis(n: usize, existing_moduli: &[u64], count: usize) -> RnsBasis {
    let aux_moduli = generate_primes_near(n, 60, existing_moduli, count);
    RnsBasis::new(n, aux_moduli)
}

pub fn generate_primes_near(
    n: usize,
    bits: u32,
    existing_moduli: &[u64],
    count: usize,
) -> Vec<u64> {
    assert!(bits >= 10 && bits <= 61);
    let two_n = 2 * (n as u64);
    let mut candidate = ((1u64 << bits) / two_n) * two_n + 1;
    let mut out = Vec::with_capacity(count);
    while out.len() < count {
        if candidate > two_n + 1 {
            candidate -= two_n;
        } else {
            panic!("exhausted candidate primes for RNS basis");
        }
        if !existing_moduli.contains(&candidate)
            && !out.contains(&candidate)
            && is_prime_u64(candidate)
            && existing_moduli.iter().all(|&q| gcd_u64(q, candidate) == 1)
            && out.iter().all(|&q| gcd_u64(q, candidate) == 1)
        {
            out.push(candidate);
        }
    }
    out
}

pub use crate::lwe::math::is_prime_u64;
