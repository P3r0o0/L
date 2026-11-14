use crate::fhe::rns::{
    generate_aux_basis, scale_mod_switch_drop_last_limb, BigUint, RnsBasis, RnsPoly,
};
use crate::lwe::math::{is_gadget_covering, sample_ternary_i64, zeroize_i64_slice};
use crate::lwe::poly::Polynomial;
use alloc::vec;
use alloc::vec::Vec;
use core::cmp::Ordering;
use rand::Rng;

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RnsSecretKey {
    pub coeffs: Vec<i64>,
}

impl RnsSecretKey {
    pub fn is_well_formed(&self, n: usize) -> bool {
        self.coeffs.len() == n && self.coeffs.iter().all(|&c| c == -1 || c == 0 || c == 1)
    }

    pub fn to_rns_poly(&self, basis: &RnsBasis) -> RnsPoly {
        RnsPoly::from_signed_i64(&self.coeffs, basis)
    }

    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::with_capacity(self.coeffs.len());
        for &c in &self.coeffs {
            let is_one = (c == 1) as u8;
            let is_neg_one = ((c == -1) as u8) << 1;
            out.push(is_one | is_neg_one);
        }
        out
    }

    pub fn from_bytes(bytes: &[u8], n: usize) -> Option<Self> {
        if bytes.len() != n {
            return None;
        }
        let mut coeffs = Vec::with_capacity(n);
        for &b in bytes {
            let c = match b {
                0 => 0i64,
                1 => 1i64,
                2 => -1i64,
                _ => return None,
            };
            coeffs.push(c);
        }
        Some(Self { coeffs })
    }
}

impl Drop for RnsSecretKey {
    fn drop(&mut self) {
        for c in self.coeffs.iter_mut() {
            unsafe {
                core::ptr::write_volatile(c, 0);
            }
        }
        core::sync::atomic::compiler_fence(core::sync::atomic::Ordering::SeqCst);
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RnsPublicKey {
    pub a: RnsPoly,
    pub b: RnsPoly,
}

impl RnsPublicKey {
    pub fn is_well_formed(&self, basis: &RnsBasis) -> bool {
        self.a.is_well_formed(basis) && self.b.is_well_formed(basis)
    }

    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = self.a.to_bytes();
        out.extend_from_slice(&self.b.to_bytes());
        out
    }

    pub fn from_bytes(bytes: &[u8], basis: &RnsBasis) -> Option<Self> {
        if bytes.len() % 2 != 0 {
            return None;
        }
        let half = bytes.len() / 2;
        let a = RnsPoly::from_bytes(&bytes[..half], basis)?;
        let b = RnsPoly::from_bytes(&bytes[half..], basis)?;
        Some(Self { a, b })
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RnsCiphertext {
    pub c0: RnsPoly,
    pub c1: RnsPoly,
}

impl RnsCiphertext {
    pub fn is_well_formed(&self, basis: &RnsBasis) -> bool {
        self.c0.is_well_formed(basis) && self.c1.is_well_formed(basis)
    }

    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = self.c0.to_bytes();
        out.extend_from_slice(&self.c1.to_bytes());
        out
    }

    pub fn from_bytes(bytes: &[u8], basis: &RnsBasis) -> Option<Self> {
        if bytes.len() % 2 != 0 {
            return None;
        }
        let half = bytes.len() / 2;
        let c0 = RnsPoly::from_bytes(&bytes[..half], basis)?;
        let c1 = RnsPoly::from_bytes(&bytes[half..], basis)?;
        Some(Self { c0, c1 })
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RnsRelinKey {
    pub a_rk: Vec<Vec<RnsPoly>>,
    pub b_rk: Vec<Vec<RnsPoly>>,
    pub base: u64,
    pub digits_per_limb: usize,
}

impl RnsRelinKey {
    pub fn is_well_formed(&self, basis: &RnsBasis) -> bool {
        let l = basis.num_limbs();
        self.a_rk.len() == l
            && self.b_rk.len() == l
            && basis
                .moduli
                .iter()
                .all(|&qi| is_gadget_covering(self.base, self.digits_per_limb, qi))
            && self.a_rk.iter().all(|row| {
                row.len() == self.digits_per_limb && row.iter().all(|p| p.is_well_formed(basis))
            })
            && self.b_rk.iter().all(|row| {
                row.len() == self.digits_per_limb && row.iter().all(|p| p.is_well_formed(basis))
            })
    }
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct RnsGaloisKey {
    pub g: usize,
    pub a_gk: Vec<Vec<RnsPoly>>,
    pub b_gk: Vec<Vec<RnsPoly>>,
    pub base: u64,
    pub digits_per_limb: usize,
}

impl RnsGaloisKey {
    pub fn is_well_formed(&self, basis: &RnsBasis) -> bool {
        let l = basis.num_limbs();
        self.g % 2 == 1
            && self.a_gk.len() == l
            && self.b_gk.len() == l
            && basis
                .moduli
                .iter()
                .all(|&qi| is_gadget_covering(self.base, self.digits_per_limb, qi))
            && self.a_gk.iter().all(|row| {
                row.len() == self.digits_per_limb && row.iter().all(|p| p.is_well_formed(basis))
            })
            && self.b_gk.iter().all(|row| {
                row.len() == self.digits_per_limb && row.iter().all(|p| p.is_well_formed(basis))
            })
    }
}

pub struct RnsBFVContext {
    pub basis: RnsBasis,
    pub aux_basis: RnsBasis,
    pub combined_basis: RnsBasis,
    pub t: u64,
    pub delta_big: BigUint,
    pub delta_residues: Vec<u64>,
}

impl RnsBFVContext {
    pub fn new(n: usize, moduli: Vec<u64>, t: u64) -> Self {
        assert!(t > 1, "Plaintext modulus t must be > 1");
        let basis = RnsBasis::new(n, moduli.clone());
        let aux_basis = generate_aux_basis(n, &moduli, moduli.len() + 1);
        let mut comb_moduli = moduli;
        comb_moduli.extend_from_slice(&aux_basis.moduli);
        let combined_basis = RnsBasis::new(n, comb_moduli);

        let (delta_big, rem_t) = basis.big_q.div_rem_u64(t);
        assert!(!delta_big.is_zero(), "Product modulus Q must exceed t");
        let two_bias = BigUint::from_u64(rem_t).mul_u64(t - 1).mul_u64(2);
        assert!(
            basis.big_q.cmp(&two_bias) == Ordering::Greater,
            "RNS-BFV parameters violate rounding-decryption margin 2*(Q mod t)*(t-1) < Q"
        );
        let delta_residues = basis
            .moduli
            .iter()
            .map(|&qi| delta_big.rem_u64(qi))
            .collect();

        Self {
            basis,
            aux_basis,
            combined_basis,
            t,
            delta_big,
            delta_residues,
        }
    }

    pub fn encode_plain(&self, pt: &Polynomial) -> RnsPoly {
        assert_eq!(pt.coeffs.len(), self.basis.n);
        let limbs = (0..self.basis.num_limbs())
            .map(|i| {
                let qi = self.basis.moduli[i];
                let d_i = self.delta_residues[i];
                let b = &self.basis.barretts[i];
                let coeffs = pt
                    .coeffs
                    .iter()
                    .map(|&m| b.mul_mod(m % self.t, d_i % qi))
                    .collect();
                Polynomial::new(coeffs)
            })
            .collect();
        RnsPoly { limbs }
    }

    #[cfg(feature = "std")]
    pub fn keygen(&self) -> (RnsSecretKey, RnsPublicKey) {
        let mut rng = rand::thread_rng();
        self.keygen_with_rng(&mut rng)
    }

    pub fn keygen_with_rng<R: Rng>(&self, rng: &mut R) -> (RnsSecretKey, RnsPublicKey) {
        let s_coeffs = self.gen_ternary_coeffs(rng);
        let sk = RnsSecretKey { coeffs: s_coeffs };
        let mut s_rns = sk.to_rns_poly(&self.basis);
        let a = self.gen_uniform_rns(rng);
        let mut e = self.gen_ternary_rns(rng);
        let mut as_plus_e = a.mul_ntt(&s_rns, &self.basis).add(&e, &self.basis);
        let b = as_plus_e.neg(&self.basis);
        s_rns.zeroize();
        e.zeroize();
        as_plus_e.zeroize();
        (sk, RnsPublicKey { a, b })
    }

    #[cfg(feature = "std")]
    pub fn encrypt(&self, pk: &RnsPublicKey, pt: &Polynomial) -> RnsCiphertext {
        let mut rng = rand::thread_rng();
        self.encrypt_with_rng(&mut rng, pk, pt)
    }

    pub fn encrypt_with_rng<R: Rng>(
        &self,
        rng: &mut R,
        pk: &RnsPublicKey,
        pt: &Polynomial,
    ) -> RnsCiphertext {
        assert!(
            pk.is_well_formed(&self.basis),
            "PublicKey must be well-formed in RnsBFVContext::encrypt"
        );
        let mut u = self.gen_ternary_rns(rng);
        let mut e0 = self.gen_ternary_rns(rng);
        let mut e1 = self.gen_ternary_rns(rng);
        let mut delta_m = self.encode_plain(pt);

        let c0 =
            pk.b.mul_ntt(&u, &self.basis)
                .add(&e0, &self.basis)
                .add(&delta_m, &self.basis);
        let c1 = pk.a.mul_ntt(&u, &self.basis).add(&e1, &self.basis);
        u.zeroize();
        e0.zeroize();
        e1.zeroize();
        delta_m.zeroize();
        RnsCiphertext { c0, c1 }
    }

    pub fn phase(&self, sk: &RnsSecretKey, ct: &RnsCiphertext) -> RnsPoly {
        assert!(
            sk.is_well_formed(self.basis.n) && ct.is_well_formed(&self.basis),
            "SecretKey and Ciphertext must be well-formed in RnsBFVContext::phase"
        );
        let mut s_rns = sk.to_rns_poly(&self.basis);
        let mut c1s = ct.c1.mul_ntt(&s_rns, &self.basis);
        let out = ct.c0.add(&c1s, &self.basis);
        s_rns.zeroize();
        c1s.zeroize();
        out
    }

    pub fn decrypt(&self, sk: &RnsSecretKey, ct: &RnsCiphertext) -> Polynomial {
        let mut phase = self.phase(sk, ct);
        let half_q = self.basis.big_q.shr1();
        let mut m_coeffs = Vec::with_capacity(self.basis.n);
        for k in 0..self.basis.n {
            let residues = phase.coeff_residues(k);
            let val_big = self.basis.crt_reconstruct_coeff(&residues);
            let num = val_big.mul_u64(self.t).add(&half_q);
            let (quot, _) = num.div_rem_big(&self.basis.big_q);
            m_coeffs.push(quot.rem_u64(self.t));
        }
        phase.zeroize();
        Polynomial::new(m_coeffs)
    }

    pub fn noise_norm_big(
        &self,
        sk: &RnsSecretKey,
        ct: &RnsCiphertext,
        pt: &Polynomial,
    ) -> BigUint {
        let mut phase = self.phase(sk, ct);
        let mut delta_m = self.encode_plain(pt);
        let mut err = phase.sub(&delta_m, &self.basis);
        let norm = err.norm_inf_big(&self.basis);
        phase.zeroize();
        delta_m.zeroize();
        err.zeroize();
        norm
    }

    pub fn noise_budget_bits(&self, sk: &RnsSecretKey, ct: &RnsCiphertext, pt: &Polynomial) -> u32 {
        let e_norm = self.noise_norm_big(sk, ct, pt);
        let rem_t = self.basis.big_q.rem_u64(self.t);
        let two_bias = BigUint::from_u64(rem_t).mul_u64(self.t - 1).mul_u64(2);
        if self.basis.big_q.cmp(&two_bias) != Ordering::Greater {
            return 0;
        }
        let avail = self.basis.big_q.sub(&two_bias);
        let two_t_e = e_norm.mul_u64(self.t).mul_u64(2);
        if avail.cmp(&two_t_e) != Ordering::Greater {
            return 0;
        }
        let (e_max, _) = avail.sub(&BigUint::from_u64(1)).div_rem_u64(2 * self.t);
        if e_max.is_zero() || e_norm.cmp(&e_max) == Ordering::Greater {
            return 0;
        }
        if e_norm.is_zero() {
            return e_max.bit_len().saturating_sub(1) as u32;
        }
        let max_bits = e_max.to_f64_log2();
        let e_bits = e_norm.to_f64_log2();
        if max_bits <= e_bits {
            0
        } else {
            (max_bits - e_bits) as u32
        }
    }

    pub fn add(&self, ct1: &RnsCiphertext, ct2: &RnsCiphertext) -> RnsCiphertext {
        assert!(
            ct1.is_well_formed(&self.basis) && ct2.is_well_formed(&self.basis),
            "Ciphertexts must be well-formed in RnsBFVContext::add"
        );
        RnsCiphertext {
            c0: ct1.c0.add(&ct2.c0, &self.basis),
            c1: ct1.c1.add(&ct2.c1, &self.basis),
        }
    }

    pub fn sub(&self, ct1: &RnsCiphertext, ct2: &RnsCiphertext) -> RnsCiphertext {
        assert!(
            ct1.is_well_formed(&self.basis) && ct2.is_well_formed(&self.basis),
            "Ciphertexts must be well-formed in RnsBFVContext::sub"
        );
        RnsCiphertext {
            c0: ct1.c0.sub(&ct2.c0, &self.basis),
            c1: ct1.c1.sub(&ct2.c1, &self.basis),
        }
    }

    pub fn add_plain(&self, ct: &RnsCiphertext, pt: &Polynomial) -> RnsCiphertext {
        assert!(
            ct.is_well_formed(&self.basis),
            "Ciphertext must be well-formed in RnsBFVContext::add_plain"
        );
        let dm = self.encode_plain(pt);
        RnsCiphertext {
            c0: ct.c0.add(&dm, &self.basis),
            c1: ct.c1.clone(),
        }
    }

    pub fn mul_plain(&self, ct: &RnsCiphertext, pt: &Polynomial) -> RnsCiphertext {
        assert!(
            ct.is_well_formed(&self.basis),
            "Ciphertext must be well-formed in RnsBFVContext::mul_plain"
        );
        let pt_rns = RnsPoly::from_single_poly(pt, &self.basis);
        RnsCiphertext {
            c0: ct.c0.mul_ntt(&pt_rns, &self.basis),
            c1: ct.c1.mul_ntt(&pt_rns, &self.basis),
        }
    }

    #[cfg(feature = "std")]
    pub fn keygen_relin(
        &self,
        sk: &RnsSecretKey,
        base: u64,
        digits_per_limb: usize,
    ) -> RnsRelinKey {
        let mut rng = rand::thread_rng();
        self.keygen_relin_with_rng(&mut rng, sk, base, digits_per_limb)
    }

    pub fn keygen_relin_with_rng<R: Rng>(
        &self,
        rng: &mut R,
        sk: &RnsSecretKey,
        base: u64,
        digits_per_limb: usize,
    ) -> RnsRelinKey {
        assert!(
            sk.is_well_formed(self.basis.n),
            "SecretKey must be well-formed in RnsBFVContext::keygen_relin"
        );
        assert!(
            self.basis
                .moduli
                .iter()
                .all(|&qi| is_gadget_covering(base, digits_per_limb, qi)),
            "Gadget parameters (base={base}, digits_per_limb={digits_per_limb}) must satisfy base^digits_per_limb >= q_i for all RNS limbs"
        );
        let mut s_rns = sk.to_rns_poly(&self.basis);
        let mut s2 = s_rns.mul_ntt(&s_rns, &self.basis);
        let (a_rk, b_rk) = self.keygen_switching_matrix(rng, &s_rns, &s2, base, digits_per_limb);
        s_rns.zeroize();
        s2.zeroize();
        RnsRelinKey {
            a_rk,
            b_rk,
            base,
            digits_per_limb,
        }
    }

    fn keygen_switching_matrix<R: Rng>(
        &self,
        rng: &mut R,
        s_rns: &RnsPoly,
        target: &RnsPoly,
        base: u64,
        digits_per_limb: usize,
    ) -> (Vec<Vec<RnsPoly>>, Vec<Vec<RnsPoly>>) {
        let l = self.basis.num_limbs();
        let mut a_mat = Vec::with_capacity(l);
        let mut b_mat = Vec::with_capacity(l);

        for i in 0..l {
            let mut a_row = Vec::with_capacity(digits_per_limb);
            let mut b_row = Vec::with_capacity(digits_per_limb);
            let mut pow_b = BigUint::from_u64(1);
            for _ in 0..digits_per_limb {
                let a = self.gen_uniform_rns(rng);
                let e = self.gen_ternary_rns(rng);
                let as_plus_e = a.mul_ntt(s_rns, &self.basis).add(&e, &self.basis);

                let mut scalars = Vec::with_capacity(l);
                for j in 0..l {
                    let qj = self.basis.moduli[j];
                    let g_ij = self.basis.gadget_residues[i][j];
                    let b_mod_qj = pow_b.rem_u64(qj);
                    scalars.push(self.basis.barretts[j].mul_mod(g_ij, b_mod_qj));
                }
                let scaled_target = target.scalar_mul_limbs(&scalars, &self.basis);
                let b = scaled_target.sub(&as_plus_e, &self.basis);

                a_row.push(a);
                b_row.push(b);
                pow_b = pow_b.mul_u64(base);
            }
            a_mat.push(a_row);
            b_mat.push(b_row);
        }

        (a_mat, b_mat)
    }

    fn apply_switching_matrix(
        &self,
        poly: &RnsPoly,
        a_mat: &[Vec<RnsPoly>],
        b_mat: &[Vec<RnsPoly>],
        base: u64,
        digits_per_limb: usize,
    ) -> (RnsPoly, RnsPoly) {
        let l = self.basis.num_limbs();
        let n = self.basis.n;
        let mut sum_a = RnsPoly::zero(&self.basis);
        let mut sum_b = RnsPoly::zero(&self.basis);

        for i in 0..l {
            let limb_poly = &poly.limbs[i];
            let mut rem_coeffs = limb_poly.coeffs.clone();
            for m in 0..digits_per_limb {
                let mut digit_coeffs = Vec::with_capacity(n);
                for val in rem_coeffs.iter_mut() {
                    digit_coeffs.push(*val % base);
                    *val /= base;
                }
                let digit_rns =
                    RnsPoly::from_single_poly(&Polynomial::new(digit_coeffs), &self.basis);
                sum_a = sum_a.add(&digit_rns.mul_ntt(&a_mat[i][m], &self.basis), &self.basis);
                sum_b = sum_b.add(&digit_rns.mul_ntt(&b_mat[i][m], &self.basis), &self.basis);
            }
        }

        (sum_a, sum_b)
    }

    fn extend_poly_to_aux(&self, poly: &RnsPoly) -> RnsPoly {
        let n = self.basis.n;
        let l_aux = self.aux_basis.num_limbs();
        let mut aux_limbs = vec![Polynomial::zero(n); l_aux];
        for k in 0..n {
            let residues = poly.coeff_residues(k);
            let ext = self
                .basis
                .bconv_exact_coeff(&residues, &self.aux_basis.moduli);
            for j in 0..l_aux {
                aux_limbs[j].coeffs[k] = ext[j];
            }
        }
        RnsPoly { limbs: aux_limbs }
    }

    fn scale_extended_product(&self, prod_q: &RnsPoly, prod_aux: &RnsPoly) -> RnsPoly {
        let n = self.basis.n;
        let l_q = self.basis.num_limbs();
        let l_aux = self.aux_basis.num_limbs();
        let half_q = self.basis.big_q.shr1();
        let mut out_limbs = vec![Polynomial::zero(n); l_q];

        for k in 0..n {
            let mut comb_residues = Vec::with_capacity(l_q + l_aux);
            for i in 0..l_q {
                comb_residues.push(prod_q.limbs[i].coeffs[k]);
            }
            for j in 0..l_aux {
                comb_residues.push(prod_aux.limbs[j].coeffs[k]);
            }
            let (abs_big, is_neg) = self
                .combined_basis
                .crt_reconstruct_centered_magnitude_and_sign(&comb_residues);
            let num = abs_big.mul_u64(self.t).add(&half_q);
            let (quot, _) = num.div_rem_big(&self.basis.big_q);
            let abs_mod_q = quot.rem_big(&self.basis.big_q);

            for i in 0..l_q {
                let qi = self.basis.moduli[i];
                let r = abs_mod_q.rem_u64(qi);
                out_limbs[i].coeffs[k] = if !is_neg || r == 0 { r } else { qi - r };
            }
        }

        RnsPoly { limbs: out_limbs }
    }

    pub fn mul(&self, ct1: &RnsCiphertext, ct2: &RnsCiphertext, rk: &RnsRelinKey) -> RnsCiphertext {
        assert!(
            ct1.is_well_formed(&self.basis)
                && ct2.is_well_formed(&self.basis)
                && rk.is_well_formed(&self.basis),
            "Ciphertexts and RnsRelinKey must be well-formed (including base^digits_per_limb >= q_i) in RnsBFVContext::mul"
        );
        let c1_0_aux = self.extend_poly_to_aux(&ct1.c0);
        let c1_1_aux = self.extend_poly_to_aux(&ct1.c1);
        let c2_0_aux = self.extend_poly_to_aux(&ct2.c0);
        let c2_1_aux = self.extend_poly_to_aux(&ct2.c1);

        let d0_q = ct1.c0.mul_ntt(&ct2.c0, &self.basis);
        let d0_aux = c1_0_aux.mul_ntt(&c2_0_aux, &self.aux_basis);

        let d1_q = ct1
            .c0
            .mul_ntt(&ct2.c1, &self.basis)
            .add(&ct1.c1.mul_ntt(&ct2.c0, &self.basis), &self.basis);
        let d1_aux = c1_0_aux.mul_ntt(&c2_1_aux, &self.aux_basis).add(
            &c1_1_aux.mul_ntt(&c2_0_aux, &self.aux_basis),
            &self.aux_basis,
        );

        let d2_q = ct1.c1.mul_ntt(&ct2.c1, &self.basis);
        let d2_aux = c1_1_aux.mul_ntt(&c2_1_aux, &self.aux_basis);

        let d0 = self.scale_extended_product(&d0_q, &d0_aux);
        let d1 = self.scale_extended_product(&d1_q, &d1_aux);
        let d2 = self.scale_extended_product(&d2_q, &d2_aux);

        let (sum_a, sum_b) =
            self.apply_switching_matrix(&d2, &rk.a_rk, &rk.b_rk, rk.base, rk.digits_per_limb);

        RnsCiphertext {
            c0: d0.add(&sum_b, &self.basis),
            c1: d1.add(&sum_a, &self.basis),
        }
    }

    pub fn modulus_switch_drop_limb(&self, ct: &RnsCiphertext) -> (RnsBFVContext, RnsCiphertext) {
        assert!(
            ct.is_well_formed(&self.basis) && self.basis.num_limbs() > 1,
            "Ciphertext must be well-formed and basis must have > 1 limb in modulus_switch_drop_limb"
        );
        let next_moduli = self.basis.moduli[..self.basis.num_limbs() - 1].to_vec();
        let next_ctx = RnsBFVContext::new(self.basis.n, next_moduli, self.t);
        let c0 = scale_mod_switch_drop_last_limb(&ct.c0, &self.basis);
        let c1 = scale_mod_switch_drop_last_limb(&ct.c1, &self.basis);
        (next_ctx, RnsCiphertext { c0, c1 })
    }

    #[cfg(feature = "std")]
    pub fn keygen_galois(
        &self,
        sk: &RnsSecretKey,
        g: usize,
        base: u64,
        digits_per_limb: usize,
    ) -> RnsGaloisKey {
        let mut rng = rand::thread_rng();
        self.keygen_galois_with_rng(&mut rng, sk, g, base, digits_per_limb)
    }

    pub fn keygen_galois_with_rng<R: Rng>(
        &self,
        rng: &mut R,
        sk: &RnsSecretKey,
        g: usize,
        base: u64,
        digits_per_limb: usize,
    ) -> RnsGaloisKey {
        assert!(g % 2 == 1, "Galois exponent g must be odd");
        assert!(
            sk.is_well_formed(self.basis.n),
            "SecretKey must be well-formed in RnsBFVContext::keygen_galois"
        );
        assert!(
            self.basis
                .moduli
                .iter()
                .all(|&qi| is_gadget_covering(base, digits_per_limb, qi)),
            "Gadget parameters (base={base}, digits_per_limb={digits_per_limb}) must satisfy base^digits_per_limb >= q_i for all RNS limbs"
        );
        let mut s_rns = sk.to_rns_poly(&self.basis);
        let mut s_galois = s_rns.apply_galois(g, &self.basis);
        let (a_gk, b_gk) =
            self.keygen_switching_matrix(rng, &s_rns, &s_galois, base, digits_per_limb);
        s_rns.zeroize();
        s_galois.zeroize();
        RnsGaloisKey {
            g,
            a_gk,
            b_gk,
            base,
            digits_per_limb,
        }
    }

    pub fn apply_galois(&self, ct: &RnsCiphertext, gk: &RnsGaloisKey) -> RnsCiphertext {
        assert!(
            ct.is_well_formed(&self.basis) && gk.is_well_formed(&self.basis),
            "Ciphertext and RnsGaloisKey must be well-formed in RnsBFVContext::apply_galois"
        );
        let c0_g = ct.c0.apply_galois(gk.g, &self.basis);
        let c1_g = ct.c1.apply_galois(gk.g, &self.basis);
        let (sum_a, sum_b) =
            self.apply_switching_matrix(&c1_g, &gk.a_gk, &gk.b_gk, gk.base, gk.digits_per_limb);
        RnsCiphertext {
            c0: c0_g.add(&sum_b, &self.basis),
            c1: sum_a,
        }
    }

    fn gen_uniform_rns<R: Rng>(&self, rng: &mut R) -> RnsPoly {
        let limbs = self
            .basis
            .moduli
            .iter()
            .map(|&qi| {
                let coeffs = (0..self.basis.n).map(|_| rng.gen_range(0..qi)).collect();
                Polynomial::new(coeffs)
            })
            .collect();
        RnsPoly { limbs }
    }

    fn gen_ternary_coeffs<R: Rng>(&self, rng: &mut R) -> Vec<i64> {
        (0..self.basis.n).map(|_| sample_ternary_i64(rng)).collect()
    }

    fn gen_ternary_rns<R: Rng>(&self, rng: &mut R) -> RnsPoly {
        let mut coeffs = self.gen_ternary_coeffs(rng);
        let poly = RnsPoly::from_signed_i64(&coeffs, &self.basis);
        zeroize_i64_slice(&mut coeffs);
        poly
    }
}
