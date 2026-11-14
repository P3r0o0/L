use crate::fhe::rns::{scale_mod_switch_drop_last_limb, BigUint, RnsBasis, RnsPoly};
use crate::fhe::rns_bfv::{RnsGaloisKey, RnsPublicKey, RnsRelinKey, RnsSecretKey};
use crate::lwe::math::{is_gadget_covering, sample_ternary_i64, zeroize_i64_slice};
use crate::lwe::poly::Polynomial;
use alloc::vec::Vec;
use core::cmp::Ordering;
use core::f64::consts::PI;
use rand::Rng;

#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Complex64 {
    pub re: f64,
    pub im: f64,
}

impl Complex64 {
    pub fn new(re: f64, im: f64) -> Self {
        Self { re, im }
    }

    pub fn from_real(re: f64) -> Self {
        Self { re, im: 0.0 }
    }

    pub fn conj(self) -> Self {
        Self {
            re: self.re,
            im: -self.im,
        }
    }

    pub fn add(self, other: Self) -> Self {
        Self {
            re: self.re + other.re,
            im: self.im + other.im,
        }
    }

    pub fn sub(self, other: Self) -> Self {
        Self {
            re: self.re - other.re,
            im: self.im - other.im,
        }
    }

    pub fn mul(self, other: Self) -> Self {
        Self {
            re: self.re * other.re - self.im * other.im,
            im: self.re * other.im + self.im * other.re,
        }
    }

    pub fn scale(self, s: f64) -> Self {
        Self {
            re: self.re * s,
            im: self.im * s,
        }
    }

    pub fn norm_sq(self) -> f64 {
        self.re * self.re + self.im * self.im
    }
}

fn sin_cos_reduced(x: f64) -> (f64, f64) {
    let x2 = x * x;
    let mut sin_sum = x;
    let mut sin_term = x;
    let mut cos_sum = 1.0;
    let mut cos_term = 1.0;
    for k in 1..=10 {
        let d_cos = ((2 * k - 1) * (2 * k)) as f64;
        cos_term = -cos_term * x2 / d_cos;
        cos_sum += cos_term;

        let d_sin = ((2 * k) * (2 * k + 1)) as f64;
        sin_term = -sin_term * x2 / d_sin;
        sin_sum += sin_term;
    }
    (sin_sum, cos_sum)
}

pub fn root_of_unity_2n(exp: usize, n: usize) -> Complex64 {
    let two_n = 2 * n;
    let m = exp % two_n;
    let half_n = n / 2;
    if n == 1 {
        return if m == 0 {
            Complex64::new(1.0, 0.0)
        } else {
            Complex64::new(-1.0, 0.0)
        };
    }
    let quadrant = m / half_n;
    let rem = m % half_n;
    let angle = PI * (rem as f64) / (n as f64);
    let (s, c) = sin_cos_reduced(angle);
    match quadrant {
        0 => Complex64::new(c, s),
        1 => Complex64::new(-s, c),
        2 => Complex64::new(-c, -s),
        _ => Complex64::new(s, -c),
    }
}

fn round_f64_to_i64(x: f64) -> i64 {
    if x >= 0.0 {
        (x + 0.5) as i64
    } else {
        (x - 0.5) as i64
    }
}

fn biguint_to_f64(b: &BigUint) -> f64 {
    let mut acc = 0.0f64;
    let base = (1u128 << 64) as f64;
    for &limb in b.limbs.iter().rev() {
        acc = acc * base + (limb as f64);
    }
    acc
}

#[derive(Clone, Debug)]
pub struct CKKSEncoder {
    pub n: usize,
    pub slots: usize,
    pub root_exponents: Vec<usize>,
}

impl CKKSEncoder {
    pub fn new(n: usize) -> Self {
        assert!(
            n >= 2 && n.is_power_of_two(),
            "CKKS degree N must be a power of two >= 2"
        );
        let slots = n / 2;
        let two_n = 2 * n;
        let mut root_exponents = Vec::with_capacity(slots);
        let mut cur = 1usize;
        for _ in 0..slots {
            root_exponents.push(cur);
            cur = (cur * 5) % two_n;
        }
        Self {
            n,
            slots,
            root_exponents,
        }
    }

    pub fn encode(&self, values: &[Complex64], scale: f64, basis: &RnsBasis) -> RnsPoly {
        assert_eq!(values.len(), self.slots);
        assert_eq!(basis.n, self.n);
        let two_n = 2 * self.n;
        let inv_n_2 = 2.0 / (self.n as f64);
        let mut coeffs = Vec::with_capacity(self.n);

        for k in 0..self.n {
            let mut sum_re = 0.0;
            for j in 0..self.slots {
                let r = self.root_exponents[j];
                let neg_rk = (two_n - ((r * k) % two_n)) % two_n;
                let w = root_of_unity_2n(neg_rk, self.n);
                let prod = values[j].mul(w);
                sum_re += prod.re;
            }
            let scaled = sum_re * inv_n_2 * scale;
            coeffs.push(round_f64_to_i64(scaled));
        }

        RnsPoly::from_signed_i64(&coeffs, basis)
    }

    pub fn decode(&self, poly: &RnsPoly, scale: f64, basis: &RnsBasis) -> Vec<Complex64> {
        assert_eq!(basis.n, self.n);
        let two_n = 2 * self.n;
        let mut real_coeffs = Vec::with_capacity(self.n);

        for k in 0..self.n {
            let residues = poly.coeff_residues(k);
            let (mag, is_neg) = basis.crt_reconstruct_centered_magnitude_and_sign(&residues);
            let val = biguint_to_f64(&mag) / scale;
            real_coeffs.push(if is_neg { -val } else { val });
        }

        let mut out = Vec::with_capacity(self.slots);
        for j in 0..self.slots {
            let r = self.root_exponents[j];
            let mut acc = Complex64::new(0.0, 0.0);
            for k in 0..self.n {
                let rk = (r * k) % two_n;
                let w = root_of_unity_2n(rk, self.n);
                acc = acc.add(w.scale(real_coeffs[k]));
            }
            out.push(acc);
        }
        out
    }
}

#[derive(Clone, Debug, PartialEq)]
pub struct CKKSCiphertext {
    pub c0: RnsPoly,
    pub c1: RnsPoly,
    pub scale: f64,
}

impl CKKSCiphertext {
    pub fn is_well_formed(&self, basis: &RnsBasis) -> bool {
        self.c0.is_well_formed(basis)
            && self.c1.is_well_formed(basis)
            && self.scale.is_finite()
            && self.scale > 0.0
    }
}

pub struct CKKSContext {
    pub basis: RnsBasis,
    pub encoder: CKKSEncoder,
}

impl CKKSContext {
    pub fn new(n: usize, moduli: Vec<u64>) -> Self {
        let basis = RnsBasis::new(n, moduli);
        let encoder = CKKSEncoder::new(n);
        Self { basis, encoder }
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
    pub fn encrypt(&self, pk: &RnsPublicKey, slots: &[Complex64], scale: f64) -> CKKSCiphertext {
        let mut rng = rand::thread_rng();
        self.encrypt_with_rng(&mut rng, pk, slots, scale)
    }

    pub fn encrypt_with_rng<R: Rng>(
        &self,
        rng: &mut R,
        pk: &RnsPublicKey,
        slots: &[Complex64],
        scale: f64,
    ) -> CKKSCiphertext {
        assert!(
            pk.is_well_formed(&self.basis),
            "PublicKey must be well-formed in CKKSContext::encrypt"
        );
        assert!(
            scale.is_finite() && scale > 0.0,
            "Scale must be finite and positive in CKKSContext::encrypt"
        );
        let mut m_poly = self.encoder.encode(slots, scale, &self.basis);
        let mut u = self.gen_ternary_rns(rng);
        let mut e0 = self.gen_ternary_rns(rng);
        let mut e1 = self.gen_ternary_rns(rng);

        let c0 =
            pk.b.mul_ntt(&u, &self.basis)
                .add(&e0, &self.basis)
                .add(&m_poly, &self.basis);
        let c1 = pk.a.mul_ntt(&u, &self.basis).add(&e1, &self.basis);
        m_poly.zeroize();
        u.zeroize();
        e0.zeroize();
        e1.zeroize();
        CKKSCiphertext { c0, c1, scale }
    }

    pub fn phase(&self, sk: &RnsSecretKey, ct: &CKKSCiphertext) -> RnsPoly {
        assert!(
            sk.is_well_formed(self.basis.n) && ct.is_well_formed(&self.basis),
            "SecretKey and CKKSCiphertext must be well-formed in CKKSContext::phase"
        );
        let mut s_rns = sk.to_rns_poly(&self.basis);
        let mut c1s = ct.c1.mul_ntt(&s_rns, &self.basis);
        let out = ct.c0.add(&c1s, &self.basis);
        s_rns.zeroize();
        c1s.zeroize();
        out
    }

    pub fn decrypt(&self, sk: &RnsSecretKey, ct: &CKKSCiphertext) -> Vec<Complex64> {
        let mut phase = self.phase(sk, ct);
        let slots = self.encoder.decode(&phase, ct.scale, &self.basis);
        phase.zeroize();
        slots
    }

    #[cfg(feature = "std")]
    pub fn decrypt_with_noise_flooding(
        &self,
        sk: &RnsSecretKey,
        ct: &CKKSCiphertext,
        flood_bits: u32,
    ) -> Vec<Complex64> {
        let mut rng = rand::thread_rng();
        self.decrypt_with_noise_flooding_and_rng(&mut rng, sk, ct, flood_bits)
    }

    pub fn decrypt_with_noise_flooding_and_rng<R: Rng>(
        &self,
        rng: &mut R,
        sk: &RnsSecretKey,
        ct: &CKKSCiphertext,
        flood_bits: u32,
    ) -> Vec<Complex64> {
        assert!(
            (1..=60).contains(&flood_bits),
            "flood_bits must be in 1..=60"
        );
        let flood_bound_4x = BigUint::from_u64(1u64 << flood_bits).mul_u64(4);
        assert!(
            flood_bound_4x.cmp(&self.basis.big_q) == Ordering::Less,
            "Modulus Q must exceed 4 * 2^flood_bits to prevent wrap-around during noise flooding"
        );

        let mut phase = self.phase(sk, ct);
        let mask = (1u64 << (flood_bits + 1)) - 1;
        let bias = 1i64 << flood_bits;
        let mut flood_coeffs: Vec<i64> = (0..self.basis.n)
            .map(|_| {
                let u = rng.next_u64() & mask;
                let b = rng.next_u64() & 1;
                (u as i64) + (b as i64) - bias
            })
            .collect();
        let mut flood_rns = RnsPoly::from_signed_i64(&flood_coeffs, &self.basis);
        zeroize_i64_slice(&mut flood_coeffs);

        let mut flooded_phase = phase.add(&flood_rns, &self.basis);
        phase.zeroize();
        flood_rns.zeroize();

        let slots = self
            .encoder
            .decode(&flooded_phase, ct.scale, &self.basis);
        flooded_phase.zeroize();
        slots
    }

    pub fn add(&self, ct1: &CKKSCiphertext, ct2: &CKKSCiphertext) -> CKKSCiphertext {
        assert!(
            ct1.is_well_formed(&self.basis) && ct2.is_well_formed(&self.basis),
            "Ciphertexts must be well-formed in CKKSContext::add"
        );
        CKKSCiphertext {
            c0: ct1.c0.add(&ct2.c0, &self.basis),
            c1: ct1.c1.add(&ct2.c1, &self.basis),
            scale: ct1.scale,
        }
    }

    pub fn sub(&self, ct1: &CKKSCiphertext, ct2: &CKKSCiphertext) -> CKKSCiphertext {
        assert!(
            ct1.is_well_formed(&self.basis) && ct2.is_well_formed(&self.basis),
            "Ciphertexts must be well-formed in CKKSContext::sub"
        );
        CKKSCiphertext {
            c0: ct1.c0.sub(&ct2.c0, &self.basis),
            c1: ct1.c1.sub(&ct2.c1, &self.basis),
            scale: ct1.scale,
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
            "SecretKey must be well-formed in CKKSContext::keygen_relin"
        );
        assert!(base >= 2 && digits_per_limb >= 1);
        assert!(
            self.basis
                .moduli
                .iter()
                .all(|&qi| is_gadget_covering(base, digits_per_limb, qi)),
            "Gadget parameters must satisfy base^digits_per_limb >= q_i for every RNS limb"
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
                let mut e = self.gen_ternary_rns(rng);
                let mut as_plus_e = a.mul_ntt(s_rns, &self.basis).add(&e, &self.basis);
                e.zeroize();

                let mut scalars = Vec::with_capacity(l);
                for j in 0..l {
                    let qj = self.basis.moduli[j];
                    let g_ij = self.basis.gadget_residues[i][j];
                    let b_mod_qj = pow_b.rem_u64(qj);
                    scalars.push(self.basis.barretts[j].mul_mod(g_ij, b_mod_qj));
                }
                let mut scaled_target = target.scalar_mul_limbs(&scalars, &self.basis);
                let b = scaled_target.sub(&as_plus_e, &self.basis);
                scaled_target.zeroize();
                as_plus_e.zeroize();

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

    pub fn mul_no_rescale(
        &self,
        ct1: &CKKSCiphertext,
        ct2: &CKKSCiphertext,
        rk: &RnsRelinKey,
    ) -> CKKSCiphertext {
        assert!(
            ct1.is_well_formed(&self.basis)
                && ct2.is_well_formed(&self.basis)
                && rk.is_well_formed(&self.basis),
            "Ciphertexts and RelinKey must be well-formed in CKKSContext::mul_no_rescale"
        );
        let d0 = ct1.c0.mul_ntt(&ct2.c0, &self.basis);
        let d1 = ct1
            .c0
            .mul_ntt(&ct2.c1, &self.basis)
            .add(&ct1.c1.mul_ntt(&ct2.c0, &self.basis), &self.basis);
        let d2 = ct1.c1.mul_ntt(&ct2.c1, &self.basis);

        let (sum_a, sum_b) =
            self.apply_switching_matrix(&d2, &rk.a_rk, &rk.b_rk, rk.base, rk.digits_per_limb);

        CKKSCiphertext {
            c0: d0.add(&sum_b, &self.basis),
            c1: d1.add(&sum_a, &self.basis),
            scale: ct1.scale * ct2.scale,
        }
    }

    pub fn rescale_drop_limb(&self, ct: &CKKSCiphertext) -> (CKKSContext, CKKSCiphertext) {
        assert!(
            ct.is_well_formed(&self.basis),
            "Ciphertext must be well-formed in CKKSContext::rescale_drop_limb"
        );
        let l = self.basis.num_limbs();
        assert!(l > 1, "Cannot rescale when only 1 RNS limb remains");
        let ql = self.basis.moduli[l - 1];
        let next_moduli = self.basis.moduli[..l - 1].to_vec();
        let next_ctx = CKKSContext::new(self.basis.n, next_moduli);
        let c0 = scale_mod_switch_drop_last_limb(&ct.c0, &self.basis);
        let c1 = scale_mod_switch_drop_last_limb(&ct.c1, &self.basis);
        let scale = ct.scale / (ql as f64);
        (next_ctx, CKKSCiphertext { c0, c1, scale })
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
        assert!(
            sk.is_well_formed(self.basis.n),
            "SecretKey must be well-formed in CKKSContext::keygen_galois"
        );
        assert!(g % 2 == 1, "Galois exponent g must be odd");
        assert!(base >= 2 && digits_per_limb >= 1);
        assert!(
            self.basis
                .moduli
                .iter()
                .all(|&qi| is_gadget_covering(base, digits_per_limb, qi)),
            "Gadget parameters must satisfy base^digits_per_limb >= q_i for every RNS limb"
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

    pub fn apply_galois(&self, ct: &CKKSCiphertext, gk: &RnsGaloisKey) -> CKKSCiphertext {
        assert!(
            ct.is_well_formed(&self.basis) && gk.is_well_formed(&self.basis),
            "Ciphertext and GaloisKey must be well-formed in CKKSContext::apply_galois"
        );
        let c0_g = ct.c0.apply_galois(gk.g, &self.basis);
        let c1_g = ct.c1.apply_galois(gk.g, &self.basis);
        let (sum_a, sum_b) =
            self.apply_switching_matrix(&c1_g, &gk.a_gk, &gk.b_gk, gk.base, gk.digits_per_limb);
        CKKSCiphertext {
            c0: c0_g.add(&sum_b, &self.basis),
            c1: sum_a,
            scale: ct.scale,
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
        (0..self.basis.n)
            .map(|_| sample_ternary_i64(rng))
            .collect()
    }

    fn gen_ternary_rns<R: Rng>(&self, rng: &mut R) -> RnsPoly {
        let mut coeffs = self.gen_ternary_coeffs(rng);
        let poly = RnsPoly::from_signed_i64(&coeffs, &self.basis);
        zeroize_i64_slice(&mut coeffs);
        poly
    }
}
