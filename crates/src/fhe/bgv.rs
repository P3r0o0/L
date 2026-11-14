use crate::fhe::rns::{gcd_u64, scale_bgv_drop_last_limb, BigUint, RnsBasis, RnsPoly};
use crate::fhe::rns_bfv::{RnsCiphertext, RnsGaloisKey, RnsPublicKey, RnsRelinKey, RnsSecretKey};
use crate::lwe::math::{is_gadget_covering, sample_ternary_i64, zeroize_i64_slice};
use crate::lwe::poly::Polynomial;
use alloc::vec;
use alloc::vec::Vec;
use core::cmp::Ordering;
use rand::Rng;

pub struct BGVContext {
    pub basis: RnsBasis,
    pub t: u64,
}

impl BGVContext {
    pub fn new(n: usize, moduli: Vec<u64>, t: u64) -> Self {
        assert!(t > 1, "Plaintext modulus t must be > 1");
        for &qi in &moduli {
            assert_eq!(
                gcd_u64(qi, t),
                1,
                "Each BGV RNS modulus q_i must be coprime to plaintext modulus t"
            );
        }
        let basis = RnsBasis::new(n, moduli);
        Self { basis, t }
    }

    pub fn encode_plain(&self, pt: &Polynomial) -> RnsPoly {
        assert_eq!(pt.coeffs.len(), self.basis.n);
        let reduced = Polynomial::new(pt.coeffs.iter().map(|&c| c % self.t).collect());
        RnsPoly::from_single_poly(&reduced, &self.basis)
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
        let mut e = self.gen_scaled_ternary_rns(rng);
        let mut as_plus_te = a.mul_ntt(&s_rns, &self.basis).add(&e, &self.basis);
        let b = as_plus_te.neg(&self.basis);
        s_rns.zeroize();
        e.zeroize();
        as_plus_te.zeroize();
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
            "PublicKey must be well-formed in BGVContext::encrypt"
        );
        let mut u = self.gen_ternary_rns(rng);
        let mut te0 = self.gen_scaled_ternary_rns(rng);
        let mut te1 = self.gen_scaled_ternary_rns(rng);
        let mut m_rns = self.encode_plain(pt);

        let c0 =
            pk.b.mul_ntt(&u, &self.basis)
                .add(&te0, &self.basis)
                .add(&m_rns, &self.basis);
        let c1 = pk.a.mul_ntt(&u, &self.basis).add(&te1, &self.basis);
        u.zeroize();
        te0.zeroize();
        te1.zeroize();
        m_rns.zeroize();
        RnsCiphertext { c0, c1 }
    }

    pub fn phase(&self, sk: &RnsSecretKey, ct: &RnsCiphertext) -> RnsPoly {
        assert!(
            sk.is_well_formed(self.basis.n) && ct.is_well_formed(&self.basis),
            "SecretKey and Ciphertext must be well-formed in BGVContext::phase"
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
        let mut m_coeffs = Vec::with_capacity(self.basis.n);
        for k in 0..self.basis.n {
            let residues = phase.coeff_residues(k);
            let (mag, is_neg) = self
                .basis
                .crt_reconstruct_centered_magnitude_and_sign(&residues);
            let r = mag.rem_u64(self.t);
            let m_k = if !is_neg || r == 0 { r } else { self.t - r };
            m_coeffs.push(m_k);
        }
        phase.zeroize();
        Polynomial::new(m_coeffs)
    }

    pub fn noise_budget_bits(&self, sk: &RnsSecretKey, ct: &RnsCiphertext) -> u32 {
        let mut phase = self.phase(sk, ct);
        let e_norm = phase.norm_inf_big(&self.basis);
        phase.zeroize();
        let two_e = e_norm.mul_u64(2);
        if self.basis.big_q.cmp(&two_e) != Ordering::Greater {
            return 0;
        }
        if e_norm.is_zero() {
            return self.basis.big_q.bit_len().saturating_sub(1) as u32;
        }
        let q_bits = self.basis.big_q.to_f64_log2();
        let e_bits = two_e.to_f64_log2();
        if q_bits <= e_bits {
            0
        } else {
            (q_bits - e_bits) as u32
        }
    }

    pub fn add(&self, ct1: &RnsCiphertext, ct2: &RnsCiphertext) -> RnsCiphertext {
        assert!(
            ct1.is_well_formed(&self.basis) && ct2.is_well_formed(&self.basis),
            "Ciphertexts must be well-formed in BGVContext::add"
        );
        RnsCiphertext {
            c0: ct1.c0.add(&ct2.c0, &self.basis),
            c1: ct1.c1.add(&ct2.c1, &self.basis),
        }
    }

    pub fn sub(&self, ct1: &RnsCiphertext, ct2: &RnsCiphertext) -> RnsCiphertext {
        assert!(
            ct1.is_well_formed(&self.basis) && ct2.is_well_formed(&self.basis),
            "Ciphertexts must be well-formed in BGVContext::sub"
        );
        RnsCiphertext {
            c0: ct1.c0.sub(&ct2.c0, &self.basis),
            c1: ct1.c1.sub(&ct2.c1, &self.basis),
        }
    }

    pub fn add_plain(&self, ct: &RnsCiphertext, pt: &Polynomial) -> RnsCiphertext {
        assert!(
            ct.is_well_formed(&self.basis),
            "Ciphertext must be well-formed in BGVContext::add_plain"
        );
        let m_rns = self.encode_plain(pt);
        RnsCiphertext {
            c0: ct.c0.add(&m_rns, &self.basis),
            c1: ct.c1.clone(),
        }
    }

    pub fn mul_plain(&self, ct: &RnsCiphertext, pt: &Polynomial) -> RnsCiphertext {
        assert!(
            ct.is_well_formed(&self.basis),
            "Ciphertext must be well-formed in BGVContext::mul_plain"
        );
        let m_rns = self.encode_plain(pt);
        RnsCiphertext {
            c0: ct.c0.mul_ntt(&m_rns, &self.basis),
            c1: ct.c1.mul_ntt(&m_rns, &self.basis),
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
            "SecretKey must be well-formed in BGVContext::keygen_relin"
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
                let te = self.gen_scaled_ternary_rns(rng);
                let as_plus_te = a.mul_ntt(s_rns, &self.basis).add(&te, &self.basis);

                let mut scalars = Vec::with_capacity(l);
                for j in 0..l {
                    let qj = self.basis.moduli[j];
                    let g_ij = self.basis.gadget_residues[i][j];
                    let b_mod_qj = pow_b.rem_u64(qj);
                    scalars.push(self.basis.barretts[j].mul_mod(g_ij, b_mod_qj));
                }
                let scaled_target = target.scalar_mul_limbs(&scalars, &self.basis);
                let b = scaled_target.sub(&as_plus_te, &self.basis);

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
            let mut rem_coeffs = poly.limbs[i].coeffs.clone();
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

    pub fn mul(&self, ct1: &RnsCiphertext, ct2: &RnsCiphertext, rk: &RnsRelinKey) -> RnsCiphertext {
        assert!(
            ct1.is_well_formed(&self.basis)
                && ct2.is_well_formed(&self.basis)
                && rk.is_well_formed(&self.basis),
            "Ciphertexts and RnsRelinKey must be well-formed (including base^digits_per_limb >= q_i) in BGVContext::mul"
        );
        let d0 = ct1.c0.mul_ntt(&ct2.c0, &self.basis);
        let d1 = ct1
            .c0
            .mul_ntt(&ct2.c1, &self.basis)
            .add(&ct1.c1.mul_ntt(&ct2.c0, &self.basis), &self.basis);
        let d2 = ct1.c1.mul_ntt(&ct2.c1, &self.basis);

        let (sum_a, sum_b) =
            self.apply_switching_matrix(&d2, &rk.a_rk, &rk.b_rk, rk.base, rk.digits_per_limb);

        RnsCiphertext {
            c0: d0.add(&sum_b, &self.basis),
            c1: d1.add(&sum_a, &self.basis),
        }
    }

    pub fn modulus_switch_drop_limb(&self, ct: &RnsCiphertext) -> (BGVContext, RnsCiphertext) {
        let l = self.basis.num_limbs();
        assert!(l > 1, "Cannot modulus switch when only 1 RNS limb remains");
        assert!(
            ct.is_well_formed(&self.basis),
            "Ciphertext must be well-formed in BGVContext::modulus_switch_drop_limb"
        );
        let ql = self.basis.moduli[l - 1];
        let r = ql % self.t;
        let scalars: Vec<u64> = vec![r; l];
        let c0_scaled = if r == 1 {
            ct.c0.clone()
        } else {
            ct.c0.scalar_mul_limbs(&scalars, &self.basis)
        };
        let c1_scaled = if r == 1 {
            ct.c1.clone()
        } else {
            ct.c1.scalar_mul_limbs(&scalars, &self.basis)
        };

        let next_moduli = self.basis.moduli[..l - 1].to_vec();
        let next_ctx = BGVContext::new(self.basis.n, next_moduli, self.t);
        let c0 = scale_bgv_drop_last_limb(&c0_scaled, &self.basis, self.t);
        let c1 = scale_bgv_drop_last_limb(&c1_scaled, &self.basis, self.t);
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
            "SecretKey must be well-formed in BGVContext::keygen_galois"
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
            "Ciphertext and RnsGaloisKey must be well-formed in BGVContext::apply_galois"
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

    fn gen_scaled_ternary_rns<R: Rng>(&self, rng: &mut R) -> RnsPoly {
        let t_i64 = self.t as i64;
        let mut coeffs: Vec<i64> = self
            .gen_ternary_coeffs(rng)
            .into_iter()
            .map(|c| c * t_i64)
            .collect();
        let poly = RnsPoly::from_signed_i64(&coeffs, &self.basis);
        zeroize_i64_slice(&mut coeffs);
        poly
    }
}
