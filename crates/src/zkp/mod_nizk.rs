use crate::lwe::math::{ct_eq_slice, norm, sub_mod, zeroize_nested_u64, zeroize_slice};
use crate::lwe::module_ntt::{
    matrix_ntt, matrix_ntt_table, ntt_evaluate, ntt_evaluate_table, vector_intt, vector_intt_table,
    vector_ntt, vector_ntt_table,
};
use crate::lwe::ntt::{inv_ntt, is_primitive_2nth_root, ntt, ntt_mul, NTTTable};
use crate::lwe::poly::Polynomial;
use alloc::vec;
use alloc::vec::Vec;
use rand::Rng;
use sha3::{
    digest::{ExtendableOutput, Update, XofReader},
    Shake256,
};

pub struct ModZKPParams {
    pub k: usize,
    pub l: usize,
    pub n: usize,
    pub q: u64,
    pub bound_b: u64,
    pub beta: u64,
    pub psi: u64,
    pub ntt_table: Option<NTTTable>,
}

pub struct ModZKPWitness {
    pub s: Vec<Polynomial>,
    pub e: Vec<Polynomial>,
}

impl Drop for ModZKPWitness {
    fn drop(&mut self) {
        for p in self.s.iter_mut() {
            p.zeroize();
        }
        for p in self.e.iter_mut() {
            p.zeroize();
        }
    }
}

pub struct ModZKPPublicInfo {
    pub a: Vec<Vec<Polynomial>>,
    pub t: Vec<Polynomial>,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub struct ModNIZKProof {
    pub c: Polynomial,
    pub z_s: Vec<Polynomial>,
    pub z_e: Vec<Polynomial>,
}

impl ModNIZKProof {
    pub fn to_bytes(&self) -> Vec<u8> {
        let mut out = Vec::new();
        out.extend_from_slice(&self.c.to_bytes());
        for p in &self.z_s {
            out.extend_from_slice(&p.to_bytes());
        }
        for p in &self.z_e {
            out.extend_from_slice(&p.to_bytes());
        }
        out
    }

    pub fn from_bytes(bytes: &[u8], k: usize, l: usize, n: usize, q: u64) -> Option<Self> {
        let poly_bytes = n.checked_mul(8)?;
        let total_polys = 1usize.checked_add(l)?.checked_add(k)?;
        if bytes.len() != total_polys.checked_mul(poly_bytes)? {
            return None;
        }
        let mut offset = 0;
        let c = Polynomial::from_bytes(&bytes[offset..offset + poly_bytes], n, q)?;
        if !c.is_ternary(q) {
            return None;
        }
        offset += poly_bytes;
        let mut z_s = Vec::with_capacity(l);
        for _ in 0..l {
            let p = Polynomial::from_bytes(&bytes[offset..offset + poly_bytes], n, q)?;
            offset += poly_bytes;
            z_s.push(p);
        }
        let mut z_e = Vec::with_capacity(k);
        for _ in 0..k {
            let p = Polynomial::from_bytes(&bytes[offset..offset + poly_bytes], n, q)?;
            offset += poly_bytes;
            z_e.push(p);
        }
        Some(Self { c, z_s, z_e })
    }
}

impl ModZKPParams {
    pub fn new(k: usize, l: usize, n: usize, q: u64, bound_b: u64, beta: u64, psi: u64) -> Self {
        assert!(k > 0 && l > 0 && n > 0, "Dimensions k, l, n must be > 0");
        assert!(bound_b > beta, "Masking bound_b must be strictly > beta");
        assert!(bound_b < q / 2, "Masking bound_b must be < q / 2");
        assert!(
            is_primitive_2nth_root(psi, n, q),
            "q must be an odd prime and psi must be a primitive 2N-th root of unity satisfying psi^N == -1 mod q"
        );
        let ntt_table = if n.is_power_of_two() && q < (1u64 << 62) {
            Some(NTTTable::new(n, psi, q))
        } else {
            None
        };
        Self {
            k,
            l,
            n,
            q,
            bound_b,
            beta,
            psi,
            ntt_table,
        }
    }

    pub fn expected_acceptance_rate(&self) -> f64 {
        if self.bound_b < self.beta {
            return 0.0;
        }
        let num = (2 * (self.bound_b - self.beta) + 1) as f64;
        let den = (2 * self.bound_b + 1) as f64;
        let base = num / den;
        let exp = (self.l + self.k).saturating_mul(self.n);
        let mut acc = 1.0;
        let mut b = base;
        let mut e = exp;
        while e > 0 {
            if e & 1 == 1 {
                acc *= b;
            }
            b *= b;
            e >>= 1;
        }
        acc
    }

    pub fn single_attempt_rejection_prob(&self) -> f64 {
        1.0 - self.expected_acceptance_rate()
    }

    pub fn all_attempts_rejection_prob(&self, max_attempts: usize) -> f64 {
        let reject_prob = self.single_attempt_rejection_prob();
        let mut acc = 1.0f64;
        let mut b = reject_prob;
        let mut e = max_attempts;
        while e > 0 {
            if (e & 1) == 1 {
                acc *= b;
            }
            b *= b;
            e >>= 1;
        }
        acc
    }

    pub fn unrejected_tv_distance(&self, shift_inf: u64) -> f64 {
        if shift_inf == 0 {
            return 0.0;
        }
        let span = 2 * self.bound_b + 1;
        if shift_inf >= span {
            return 1.0;
        }
        let overlap = (span - shift_inf) as f64 / (span as f64);
        let exp = (self.l + self.k).saturating_mul(self.n);
        let mut prod = 1.0f64;
        let mut b = overlap;
        let mut e = exp;
        while e > 0 {
            if (e & 1) == 1 {
                prod *= b;
            }
            b *= b;
            e >>= 1;
        }
        1.0 - prod
    }

    pub fn accepted_zk_tv_distance(&self, actual_shift_inf: u64) -> f64 {
        if actual_shift_inf <= self.beta {
            return 0.0;
        }
        let excess = actual_shift_inf - self.beta;
        let box_span = 2 * (self.bound_b - self.beta) + 1;
        if excess >= box_span {
            return 1.0;
        }
        let ratio = (box_span - excess) as f64 / (box_span as f64);
        let exp = (self.l + self.k).saturating_mul(self.n);
        let mut prod = 1.0f64;
        let mut b = ratio;
        let mut e = exp;
        while e > 0 {
            if (e & 1) == 1 {
                prod *= b;
            }
            b *= b;
            e >>= 1;
        }
        1.0 - prod
    }

    pub fn norm(&self, x: u64) -> u64 {
        norm(x, self.q)
    }

    pub fn inf_norm(&self, poly: &Polynomial) -> u64 {
        poly.norm_inf(self.q)
    }

    pub fn vec_inf_norm(&self, vec: &[Polynomial]) -> u64 {
        vec.iter().map(|p| self.inf_norm(p)).max().unwrap_or(0)
    }

    pub fn hash_to_challenge(
        &self,
        a: &[Vec<Polynomial>],
        t: &[Polynomial],
        w: &[Polynomial],
    ) -> Polynomial {
        self.hash_to_challenge_with_context(a, t, w, &[])
    }

    pub fn hash_to_challenge_with_context(
        &self,
        a: &[Vec<Polynomial>],
        t: &[Polynomial],
        w: &[Polynomial],
        context: &[u8],
    ) -> Polynomial {
        let mut hasher = Shake256::default();
        hasher.update(b"LWE-MOD-ZKP-NIZK-v1");
        hasher.update(&(self.k as u64).to_le_bytes());
        hasher.update(&(self.l as u64).to_le_bytes());
        hasher.update(&(self.n as u64).to_le_bytes());
        hasher.update(&self.q.to_le_bytes());
        hasher.update(&self.bound_b.to_le_bytes());
        hasher.update(&self.beta.to_le_bytes());
        hasher.update(&self.psi.to_le_bytes());

        for row in a {
            for poly in row {
                for &val in &poly.coeffs {
                    hasher.update(&val.to_le_bytes());
                }
            }
        }
        for poly in t {
            for &val in &poly.coeffs {
                hasher.update(&val.to_le_bytes());
            }
        }
        for poly in w {
            for &val in &poly.coeffs {
                hasher.update(&val.to_le_bytes());
            }
        }
        if !context.is_empty() {
            hasher.update(b"CTX");
            hasher.update(&(context.len() as u64).to_le_bytes());
            hasher.update(context);
        }
        let mut reader = hasher.finalize_xof();

        let mut coeffs = Vec::with_capacity(self.n);
        let mut buf = [0u8; 1];
        for _ in 0..self.n {
            loop {
                reader.read(&mut buf);
                let byte = buf[0];
                if byte < 255 {
                    let val = match byte % 3 {
                        0 => 0,
                        1 => 1,
                        _ => self.q - 1,
                    };
                    coeffs.push(val);
                    break;
                }
            }
        }
        Polynomial::new(coeffs)
    }

    #[cfg(feature = "std")]
    pub fn prove(
        &self,
        a: &[Vec<Polynomial>],
        witness: &ModZKPWitness,
    ) -> (ModZKPPublicInfo, ModNIZKProof, u32) {
        let mut rng = rand::thread_rng();
        self.prove_with_rng(&mut rng, a, witness)
    }

    #[cfg(feature = "std")]
    pub fn prove_with_context(
        &self,
        a: &[Vec<Polynomial>],
        witness: &ModZKPWitness,
        context: &[u8],
    ) -> (ModZKPPublicInfo, ModNIZKProof, u32) {
        let mut rng = rand::thread_rng();
        self.prove_with_context_and_rng(&mut rng, a, witness, context)
    }

    pub fn prove_with_rng<R: Rng>(
        &self,
        rng: &mut R,
        a: &[Vec<Polynomial>],
        witness: &ModZKPWitness,
    ) -> (ModZKPPublicInfo, ModNIZKProof, u32) {
        self.prove_with_context_and_rng(rng, a, witness, &[])
    }

    pub fn prove_with_context_and_rng<R: Rng>(
        &self,
        rng: &mut R,
        a: &[Vec<Polynomial>],
        witness: &ModZKPWitness,
        context: &[u8],
    ) -> (ModZKPPublicInfo, ModNIZKProof, u32) {
        assert_eq!(a.len(), self.k);
        for row in a {
            assert_eq!(row.len(), self.l);
            for p in row {
                assert_eq!(p.coeffs.len(), self.n);
                assert!(
                    p.is_canonical(self.q),
                    "Matrix A polynomials must have canonical coefficients < q"
                );
            }
        }
        assert_eq!(witness.s.len(), self.l);
        for p in &witness.s {
            assert_eq!(p.coeffs.len(), self.n);
            assert!(
                p.is_canonical(self.q),
                "Witness s polynomials must have canonical coefficients < q"
            );
        }
        assert_eq!(witness.e.len(), self.k);
        for p in &witness.e {
            assert_eq!(p.coeffs.len(), self.n);
            assert!(
                p.is_canonical(self.q),
                "Witness e polynomials must have canonical coefficients < q"
            );
        }
        assert!(
            self.bound_b > self.beta && self.bound_b < self.q / 2,
            "Masking bound_b must satisfy beta < bound_b < q / 2"
        );
        let max_w = self
            .vec_inf_norm(&witness.s)
            .max(self.vec_inf_norm(&witness.e));
        assert!(
            (self.n as u64)
                .checked_mul(max_w)
                .is_some_and(|req| self.beta >= req),
            "Zero-knowledge requires beta >= N * ||witness||_inf (got beta={}, N={}, ||w||_inf={})",
            self.beta,
            self.n,
            max_w
        );

        let (a_ntt, mut s_ntt, mut e_ntt, t) = if let Some(ref table) = self.ntt_table {
            let a_ntt = matrix_ntt_table(a, table);
            let s_ntt = vector_ntt_table(&witness.s, table);
            let e_ntt = vector_ntt_table(&witness.e, table);
            let t_ntt = ntt_evaluate_table(&a_ntt, &s_ntt, &e_ntt, table);
            let t = vector_intt_table(&t_ntt, table);
            (a_ntt, s_ntt, e_ntt, t)
        } else {
            let a_ntt = matrix_ntt(a, self.psi, self.q);
            let s_ntt = vector_ntt(&witness.s, self.psi, self.q);
            let e_ntt = vector_ntt(&witness.e, self.psi, self.q);
            let t_ntt = ntt_evaluate(&a_ntt, &s_ntt, &e_ntt, self.q);
            let t = vector_intt(&t_ntt, self.psi, self.q);
            (a_ntt, s_ntt, e_ntt, t)
        };

        let pub_info = ModZKPPublicInfo {
            a: a.to_vec(),
            t: t.clone(),
        };

        let span = 2 * self.bound_b;
        let mask_bits = 64 - span.leading_zeros();
        let bit_mask = if mask_bits >= 64 {
            u64::MAX
        } else {
            (1u64 << mask_bits) - 1
        };

        let sample_mask_elem = |rng: &mut R| -> u64 {
            loop {
                let cand = rng.next_u64() & bit_mask;
                if cand <= span {
                    return sub_mod(cand, self.bound_b, self.q);
                }
            }
        };

        let mut attempts = 0;

        loop {
            attempts += 1;
            let mut y_s = Vec::with_capacity(self.l);
            for _ in 0..self.l {
                let mut coeffs = Vec::with_capacity(self.n);
                for _ in 0..self.n {
                    coeffs.push(sample_mask_elem(rng));
                }
                y_s.push(Polynomial::new(coeffs));
            }

            let mut y_e = Vec::with_capacity(self.k);
            for _ in 0..self.k {
                let mut coeffs = Vec::with_capacity(self.n);
                for _ in 0..self.n {
                    coeffs.push(sample_mask_elem(rng));
                }
                y_e.push(Polynomial::new(coeffs));
            }

            let w = if let Some(ref table) = self.ntt_table {
                let mut ys_ntt = vector_ntt_table(&y_s, table);
                let mut ye_ntt = vector_ntt_table(&y_e, table);
                let w_ntt = ntt_evaluate_table(&a_ntt, &ys_ntt, &ye_ntt, table);
                zeroize_nested_u64(&mut ys_ntt);
                zeroize_nested_u64(&mut ye_ntt);
                vector_intt_table(&w_ntt, table)
            } else {
                let mut ys_ntt = vector_ntt(&y_s, self.psi, self.q);
                let mut ye_ntt = vector_ntt(&y_e, self.psi, self.q);
                let w_ntt = ntt_evaluate(&a_ntt, &ys_ntt, &ye_ntt, self.q);
                zeroize_nested_u64(&mut ys_ntt);
                zeroize_nested_u64(&mut ye_ntt);
                vector_intt(&w_ntt, self.psi, self.q)
            };

            let c = self.hash_to_challenge_with_context(a, &t, &w, context);

            let safe_bound = self.bound_b - self.beta;
            let c_ntt = if let Some(ref table) = self.ntt_table {
                table.forward(&c)
            } else {
                ntt(&c, self.psi, self.q)
            };

            let mut z_s = Vec::with_capacity(self.l);
            let mut rejected = false;
            for j in 0..self.l {
                let mut cs = if let Some(ref table) = self.ntt_table {
                    let mut cs_ntt: Vec<u64> = c_ntt
                        .iter()
                        .zip(s_ntt[j].iter())
                        .map(|(&ci, &si)| table.barrett.mul_mod(ci, si))
                        .collect();
                    let inv = table.inverse(&cs_ntt);
                    zeroize_slice(&mut cs_ntt);
                    inv
                } else {
                    let mut cs_ntt = ntt_mul(&c_ntt, &s_ntt[j], self.q);
                    let inv = inv_ntt(&cs_ntt, self.psi, self.q);
                    zeroize_slice(&mut cs_ntt);
                    inv
                };
                debug_assert!(self.inf_norm(&cs) <= self.beta);
                let z_sj = y_s[j].add(&cs, self.q);
                cs.zeroize();
                rejected |= self.inf_norm(&z_sj) > safe_bound;
                z_s.push(z_sj);
            }
            for p in y_s.iter_mut() {
                p.zeroize();
            }

            let mut z_e = Vec::with_capacity(self.k);
            for i in 0..self.k {
                let mut ce = if let Some(ref table) = self.ntt_table {
                    let mut ce_ntt: Vec<u64> = c_ntt
                        .iter()
                        .zip(e_ntt[i].iter())
                        .map(|(&ci, &ei)| table.barrett.mul_mod(ci, ei))
                        .collect();
                    let inv = table.inverse(&ce_ntt);
                    zeroize_slice(&mut ce_ntt);
                    inv
                } else {
                    let mut ce_ntt = ntt_mul(&c_ntt, &e_ntt[i], self.q);
                    let inv = inv_ntt(&ce_ntt, self.psi, self.q);
                    zeroize_slice(&mut ce_ntt);
                    inv
                };
                debug_assert!(self.inf_norm(&ce) <= self.beta);
                let z_ei = y_e[i].add(&ce, self.q);
                ce.zeroize();
                rejected |= self.inf_norm(&z_ei) > safe_bound;
                z_e.push(z_ei);
            }
            for p in y_e.iter_mut() {
                p.zeroize();
            }

            if !rejected {
                zeroize_nested_u64(&mut s_ntt);
                zeroize_nested_u64(&mut e_ntt);
                return (pub_info, ModNIZKProof { c, z_s, z_e }, attempts);
            }
            for p in z_s.iter_mut() {
                p.zeroize();
            }
            for p in z_e.iter_mut() {
                p.zeroize();
            }
        }
    }

    pub fn verify(&self, pub_info: &ModZKPPublicInfo, proof: &ModNIZKProof) -> bool {
        self.verify_with_context(pub_info, proof, &[])
    }

    pub fn verify_with_context(
        &self,
        pub_info: &ModZKPPublicInfo,
        proof: &ModNIZKProof,
        context: &[u8],
    ) -> bool {
        if self.bound_b <= self.beta || self.bound_b >= self.q / 2 {
            return false;
        }
        if pub_info.a.len() != self.k
            || !pub_info.a.iter().all(|row| {
                row.len() == self.l
                    && row
                        .iter()
                        .all(|p| p.coeffs.len() == self.n && p.is_canonical(self.q))
            })
            || pub_info.t.len() != self.k
            || !pub_info
                .t
                .iter()
                .all(|p| p.coeffs.len() == self.n && p.is_canonical(self.q))
            || proof.c.coeffs.len() != self.n
            || !proof.c.is_canonical(self.q)
            || !proof.c.is_ternary(self.q)
            || proof.z_s.len() != self.l
            || !proof
                .z_s
                .iter()
                .all(|p| p.coeffs.len() == self.n && p.is_canonical(self.q))
            || proof.z_e.len() != self.k
            || !proof
                .z_e
                .iter()
                .all(|p| p.coeffs.len() == self.n && p.is_canonical(self.q))
        {
            return false;
        }

        let safe_bound = self.bound_b - self.beta;
        if self.vec_inf_norm(&proof.z_s) > safe_bound || self.vec_inf_norm(&proof.z_e) > safe_bound
        {
            return false;
        }

        let w_prime = if let Some(ref table) = self.ntt_table {
            let a_ntt = matrix_ntt_table(&pub_info.a, table);
            let zs_ntt = vector_ntt_table(&proof.z_s, table);
            let ze_ntt = vector_ntt_table(&proof.z_e, table);
            let az_ntt = ntt_evaluate_table(&a_ntt, &zs_ntt, &ze_ntt, table);
            let c_ntt = table.forward(&proof.c);
            let t_ntt = vector_ntt_table(&pub_info.t, table);
            let mut w_prime = Vec::with_capacity(self.k);
            for i in 0..self.k {
                let mut w_i_ntt = vec![0; self.n];
                for x in 0..self.n {
                    let ct_x = table.barrett.mul_mod(c_ntt[x], t_ntt[i][x]);
                    w_i_ntt[x] = sub_mod(az_ntt[i][x], ct_x, self.q);
                }
                w_prime.push(table.inverse(&w_i_ntt));
            }
            w_prime
        } else {
            let a_ntt = matrix_ntt(&pub_info.a, self.psi, self.q);
            let zs_ntt = vector_ntt(&proof.z_s, self.psi, self.q);
            let ze_ntt = vector_ntt(&proof.z_e, self.psi, self.q);
            let az_ntt = ntt_evaluate(&a_ntt, &zs_ntt, &ze_ntt, self.q);
            let c_ntt = ntt(&proof.c, self.psi, self.q);
            let t_ntt = vector_ntt(&pub_info.t, self.psi, self.q);
            let mut w_prime = Vec::with_capacity(self.k);
            for i in 0..self.k {
                let ct_ntt = ntt_mul(&c_ntt, &t_ntt[i], self.q);
                let mut w_i_ntt = vec![0; self.n];
                for x in 0..self.n {
                    w_i_ntt[x] = sub_mod(az_ntt[i][x], ct_ntt[x], self.q);
                }
                w_prime.push(inv_ntt(&w_i_ntt, self.psi, self.q));
            }
            w_prime
        };

        let c_prime =
            self.hash_to_challenge_with_context(&pub_info.a, &pub_info.t, &w_prime, context);

        ct_eq_slice(&proof.c.coeffs, &c_prime.coeffs)
    }
}
