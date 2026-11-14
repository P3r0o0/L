use lwe::estimator::{estimate_dual_attack, estimate_primal_usvp_gsa, LweEstimateInput};
use lwe::fhe::bfv::{
    BFVContext, Ciphertext as BFVCiphertext, PublicKey as BFVPublicKey, RelinKey as BFVRelinKey,
    SecretKey as BFVSecretKey,
};
use lwe::fhe::bgv::BGVContext;
use lwe::fhe::ckks::{CKKSContext, Complex64};
use lwe::fhe::rns::{generate_aux_basis, generate_primes_near, RnsBasis, RnsPoly};
use lwe::fhe::rns_bfv::{RnsBFVContext, RnsCiphertext, RnsPublicKey, RnsSecretKey};
use lwe::lwe::poly::Polynomial;
use rand::rngs::StdRng;
use rand::{Rng, SeedableRng};

#[test]
fn test_rns_basis_crt_gadget_and_fast_bconv_identities() {
    let n = 8;
    let moduli = vec![65537u64, 114689u64, 147457u64];
    let basis = RnsBasis::new(n, moduli.clone());
    let q_total: u128 = (moduli[0] as u128) * (moduli[1] as u128) * (moduli[2] as u128);

    let mut rng = StdRng::seed_from_u64(0x1122_3344_5566_7788);
    for _ in 0..50 {
        let x: u128 = rng.gen_range(0..q_total);
        let residues: Vec<u64> = moduli.iter().map(|&qi| (x % (qi as u128)) as u64).collect();
        let rec = basis.crt_reconstruct_coeff(&residues);
        let rec_u128 = (rec.limbs.first().copied().unwrap_or(0) as u128)
            | ((rec.limbs.get(1).copied().unwrap_or(0) as u128) << 64);
        assert_eq!(rec_u128, x);

        let target_p = 786433u64;
        let fast_ext = basis.fast_bconv_coeff(&residues, &[target_p])[0];
        let exact_ext = basis.bconv_exact_coeff(&residues, &[target_p])[0];
        assert_eq!(exact_ext, (x % (target_p as u128)) as u64);

        let mut y_sum: u128 = 0;
        for i in 0..3 {
            let qi = moduli[i];
            let yi = basis.barretts[i].mul_mod(residues[i], basis.q_hat_inv_mod_qi[i]);
            let qh = q_total / (qi as u128);
            y_sum += (yi as u128) * qh;
        }
        let u = (y_sum - x) / q_total;
        assert!(u < 3);
        assert_eq!(y_sum, x + u * q_total);
        assert_eq!((y_sum % (target_p as u128)) as u64, fast_ext);
    }

    let poly_coeffs: Vec<i64> = (0..n).map(|i| (i as i64 * 12345) - 30000).collect();
    let rns_p = RnsPoly::from_signed_i64(&poly_coeffs, &basis);
    let digits = rns_p.gadget_decompose(&basis);
    let mut reconstructed = RnsPoly::zero(&basis);
    for i in 0..3 {
        let g_poly = digits[i].scalar_mul_limbs(&basis.gadget_residues[i], &basis);
        reconstructed = reconstructed.add(&g_poly, &basis);
    }
    assert_eq!(reconstructed, rns_p);
}

#[test]
fn test_rns_bfv_single_limb_exact_equivalence_with_bfv() {
    let n = 8;
    let q = 65537u64;
    let t = 17u64;

    let rns_ctx = RnsBFVContext::new(n, vec![q], t);
    let psi = rns_ctx.basis.psi[0];
    let bfv_ctx = BFVContext::new_with_ntt(n, q, t, psi);

    let s_signed = vec![1i64, -1, 0, 1, 0, -1, 1, -1];
    let rns_sk = RnsSecretKey {
        coeffs: s_signed.clone(),
    };
    let bfv_sk = BFVSecretKey(rns_sk.to_rns_poly(&rns_ctx.basis).limbs[0].clone());

    let mut rng = StdRng::seed_from_u64(0x9988_7766_5544_3322);
    let a_poly = Polynomial::new((0..n).map(|_| rng.gen_range(0..q)).collect());
    let e_signed: Vec<i64> = (0..n).map(|_| rng.gen_range(-1..=1)).collect();
    let e_rns = RnsPoly::from_signed_i64(&e_signed, &rns_ctx.basis);
    let a_rns = RnsPoly {
        limbs: vec![a_poly.clone()],
    };
    let s_rns = rns_sk.to_rns_poly(&rns_ctx.basis);
    let b_rns = a_rns
        .mul_ntt(&s_rns, &rns_ctx.basis)
        .add(&e_rns, &rns_ctx.basis)
        .neg(&rns_ctx.basis);

    let rns_pk = RnsPublicKey {
        a: a_rns,
        b: b_rns.clone(),
    };
    let _bfv_pk = BFVPublicKey {
        a: a_poly,
        b: b_rns.limbs[0].clone(),
    };

    let pt1 = Polynomial::new(vec![3, 1, 4, 1, 5, 9, 2, 6]);
    let pt2 = Polynomial::new(vec![2, 7, 1, 8, 2, 8, 1, 8]);

    let rns_ct1 = rns_ctx.encrypt_with_rng(&mut rng, &rns_pk, &pt1);
    let rns_ct2 = rns_ctx.encrypt_with_rng(&mut rng, &rns_pk, &pt2);

    let bfv_ct1 = BFVCiphertext {
        c0: rns_ct1.c0.limbs[0].clone(),
        c1: rns_ct1.c1.limbs[0].clone(),
    };
    let bfv_ct2 = BFVCiphertext {
        c0: rns_ct2.c0.limbs[0].clone(),
        c1: rns_ct2.c1.limbs[0].clone(),
    };

    let base = 16u64;
    let l_digits = 5usize;
    let rns_rk = rns_ctx.keygen_relin_with_rng(&mut rng, &rns_sk, base, l_digits);
    let bfv_rk = BFVRelinKey {
        a_rk: rns_rk.a_rk[0].iter().map(|p| p.limbs[0].clone()).collect(),
        b_rk: rns_rk.b_rk[0].iter().map(|p| p.limbs[0].clone()).collect(),
        base,
        l: l_digits,
    };

    let rns_mul = rns_ctx.mul(&rns_ct1, &rns_ct2, &rns_rk);
    let bfv_mul = bfv_ctx.mul(&bfv_ct1, &bfv_ct2, &bfv_rk);

    assert_eq!(rns_mul.c0.limbs[0], bfv_mul.c0);
    assert_eq!(rns_mul.c1.limbs[0], bfv_mul.c1);
    assert_eq!(
        rns_ctx.decrypt(&rns_sk, &rns_mul),
        bfv_ctx.decrypt(&bfv_sk, &bfv_mul)
    );
    assert_eq!(
        rns_ctx.decrypt(&rns_sk, &rns_mul),
        pt1.mul_schoolbook(&pt2, t)
    );
}

#[test]
fn test_full_rns_bfv_multi_limb_deep_mul_modswitch_and_galois() {
    let n = 16;
    let t = 17u64;
    let basis_primes = generate_aux_basis(n, &[], 4).moduli;
    let ctx = RnsBFVContext::new(n, basis_primes.clone(), t);
    assert!(ctx.basis.log2_q() > 230.0);

    let est_in = LweEstimateInput::new_rns_ternary(8192, 16384, &basis_primes);
    let gsa = estimate_primal_usvp_gsa(&est_in);
    let dual = estimate_dual_attack(&est_in);
    assert!(gsa.classical_bits > 80.0 && dual.classical_bits > 80.0);

    let mut rng = StdRng::seed_from_u64(0xABCD_1234_EF01_5678);
    let (sk, pk) = ctx.keygen_with_rng(&mut rng);
    assert!(sk.is_well_formed(n));
    assert!(pk.is_well_formed(&ctx.basis));

    let sk_bytes = sk.to_bytes();
    assert_eq!(RnsSecretKey::from_bytes(&sk_bytes, n).unwrap(), sk);
    let pk_bytes = pk.to_bytes();
    assert_eq!(RnsPublicKey::from_bytes(&pk_bytes, &ctx.basis).unwrap(), pk);

    let rk = ctx.keygen_relin_with_rng(&mut rng, &sk, 1u64 << 20, 3);
    let gk = ctx.keygen_galois_with_rng(&mut rng, &sk, 3, 1u64 << 20, 3);

    let pt1 = Polynomial::new((0..n).map(|i| ((i * 3 + 1) as u64) % t).collect());
    let pt2 = Polynomial::new((0..n).map(|i| ((i * 5 + 2) as u64) % t).collect());
    let pt3 = Polynomial::new((0..n).map(|i| ((i * 7 + 4) as u64) % t).collect());
    let pt4 = Polynomial::new((0..n).map(|i| ((i * 2 + 3) as u64) % t).collect());

    let ct1 = ctx.encrypt_with_rng(&mut rng, &pk, &pt1);
    let ct2 = ctx.encrypt_with_rng(&mut rng, &pk, &pt2);
    let ct3 = ctx.encrypt_with_rng(&mut rng, &pk, &pt3);
    let ct4 = ctx.encrypt_with_rng(&mut rng, &pk, &pt4);

    let ct1_bytes = ct1.to_bytes();
    assert_eq!(
        RnsCiphertext::from_bytes(&ct1_bytes, &ctx.basis).unwrap(),
        ct1
    );

    let budget_fresh = ctx.noise_budget_bits(&sk, &ct1, &pt1);
    assert!(budget_fresh > 200);

    let ct12 = ctx.mul(&ct1, &ct2, &rk);
    let pt12 = pt1.mul_schoolbook(&pt2, t);
    assert_eq!(ctx.decrypt(&sk, &ct12), pt12);

    let ct123 = ctx.mul(&ct12, &ct3, &rk);
    let pt123 = pt12.mul_schoolbook(&pt3, t);
    assert_eq!(ctx.decrypt(&sk, &ct123), pt123);

    let ct1234 = ctx.mul(&ct123, &ct4, &rk);
    let pt1234 = pt123.mul_schoolbook(&pt4, t);
    assert_eq!(ctx.decrypt(&sk, &ct1234), pt1234);

    let budget_after_3_muls = ctx.noise_budget_bits(&sk, &ct1234, &pt1234);
    assert!(budget_after_3_muls > 100 && budget_after_3_muls < budget_fresh);

    let ct_rot = ctx.apply_galois(&ct1, &gk);
    assert_eq!(ctx.decrypt(&sk, &ct_rot), pt1.apply_galois(3, t));

    let (ctx_lvl2, ct_lvl2) = ctx.modulus_switch_drop_limb(&ct1234);
    assert_eq!(ctx_lvl2.basis.num_limbs(), 3);
    assert_eq!(ctx_lvl2.decrypt(&sk, &ct_lvl2), pt1234);
}

#[test]
fn test_rns_bgv_homomorphic_ops_and_modulus_switching() {
    let n = 16;
    let t = 17u64;
    let moduli = vec![65537u64, 114689u64, 147457u64];
    let ctx = BGVContext::new(n, moduli, t);

    let mut rng = StdRng::seed_from_u64(0xB670_2026_1234_5678);
    let (sk, pk) = ctx.keygen_with_rng(&mut rng);
    let rk = ctx.keygen_relin_with_rng(&mut rng, &sk, 256, 3);
    let gk = ctx.keygen_galois_with_rng(&mut rng, &sk, 5, 256, 3);

    let pt1 = Polynomial::new((0..n).map(|i| ((i * 2 + 1) as u64) % t).collect());
    let pt2 = Polynomial::new((0..n).map(|i| ((i * 4 + 3) as u64) % t).collect());
    let pt3 = Polynomial::new((0..n).map(|i| ((i + 5) as u64) % t).collect());

    let ct1 = ctx.encrypt_with_rng(&mut rng, &pk, &pt1);
    let ct2 = ctx.encrypt_with_rng(&mut rng, &pk, &pt2);
    let ct3 = ctx.encrypt_with_rng(&mut rng, &pk, &pt3);

    assert_eq!(ctx.decrypt(&sk, &ct1), pt1);
    assert_eq!(ctx.decrypt(&sk, &ctx.add(&ct1, &ct2)), pt1.add(&pt2, t));
    assert_eq!(ctx.decrypt(&sk, &ctx.sub(&ct1, &ct2)), pt1.sub(&pt2, t));
    assert_eq!(
        ctx.decrypt(&sk, &ctx.add_plain(&ct1, &pt3)),
        pt1.add(&pt3, t)
    );
    assert_eq!(
        ctx.decrypt(&sk, &ctx.mul_plain(&ct1, &pt3)),
        pt1.mul_schoolbook(&pt3, t)
    );

    let ct_rot = ctx.apply_galois(&ct1, &gk);
    assert_eq!(ctx.decrypt(&sk, &ct_rot), pt1.apply_galois(5, t));

    let ct12 = ctx.mul(&ct1, &ct2, &rk);
    let pt12 = pt1.mul_schoolbook(&pt2, t);
    assert_eq!(ctx.decrypt(&sk, &ct12), pt12);

    let (ctx_lvl1, ct12_lvl1) = ctx.modulus_switch_drop_limb(&ct12);
    let (_, ct3_lvl1) = ctx.modulus_switch_drop_limb(&ct3);
    assert_eq!(ctx_lvl1.decrypt(&sk, &ct12_lvl1), pt12);
    assert_eq!(ctx_lvl1.decrypt(&sk, &ct3_lvl1), pt3);

    let rk_lvl1 = ctx_lvl1.keygen_relin_with_rng(&mut rng, &sk, 256, 3);
    let ct123_lvl1 = ctx_lvl1.mul(&ct12_lvl1, &ct3_lvl1, &rk_lvl1);
    let pt123 = pt12.mul_schoolbook(&pt3, t);
    assert_eq!(ctx_lvl1.decrypt(&sk, &ct123_lvl1), pt123);

    let (ctx_lvl0, ct123_lvl0) = ctx_lvl1.modulus_switch_drop_limb(&ct123_lvl1);
    assert_eq!(ctx_lvl0.basis.num_limbs(), 1);
    assert_eq!(ctx_lvl0.decrypt(&sk, &ct123_lvl0), pt123);
    assert!(ctx_lvl0.noise_budget_bits(&sk, &ct123_lvl0) > 0);
}

#[test]
fn test_rns_ckks_canonical_embedding_mul_rescale_and_galois() {
    let n = 16;
    let q0 = generate_primes_near(n, 55, &[], 1)[0];
    let q12 = generate_primes_near(n, 45, &[q0], 2);
    let ckks_moduli = vec![q0, q12[0], q12[1]];
    let ctx = CKKSContext::new(n, ckks_moduli.clone());
    let scale = ckks_moduli[2] as f64;

    let slots1: Vec<Complex64> = (0..8)
        .map(|i| Complex64::new(0.25 * (i as f64 + 1.0), -0.1 * (i as f64)))
        .collect();
    let slots2: Vec<Complex64> = (0..8)
        .map(|i| Complex64::new(1.5 - 0.1 * (i as f64), 0.2 * (i as f64 + 1.0)))
        .collect();

    let encoded1 = ctx.encoder.encode(&slots1, scale, &ctx.basis);
    let decoded1 = ctx.encoder.decode(&encoded1, scale, &ctx.basis);
    for (a, b) in slots1.iter().zip(decoded1.iter()) {
        assert!(a.sub(*b).norm_sq() < 1e-12);
    }

    let mut rng = StdRng::seed_from_u64(0xC445_2026_9876_5432);
    let (sk, pk) = ctx.keygen_with_rng(&mut rng);
    let rk = ctx.keygen_relin_with_rng(&mut rng, &sk, 1024, 6);
    let gk_rot = ctx.keygen_galois_with_rng(&mut rng, &sk, 5, 1024, 6);
    let gk_conj = ctx.keygen_galois_with_rng(&mut rng, &sk, 2 * n - 1, 1024, 6);

    let ct1 = ctx.encrypt_with_rng(&mut rng, &pk, &slots1, scale);
    let ct2 = ctx.encrypt_with_rng(&mut rng, &pk, &slots2, scale);

    let ct_add = ctx.add(&ct1, &ct2);
    let dec_add = ctx.decrypt(&sk, &ct_add);
    for i in 0..8 {
        let exp = slots1[i].add(slots2[i]);
        assert!(dec_add[i].sub(exp).norm_sq() < 1e-10);
    }

    let ct_rot = ctx.apply_galois(&ct1, &gk_rot);
    let dec_rot = ctx.decrypt(&sk, &ct_rot);
    for i in 0..8 {
        let exp = slots1[(i + 1) % 8];
        assert!(dec_rot[i].sub(exp).norm_sq() < 1e-10);
    }

    let ct_conj = ctx.apply_galois(&ct1, &gk_conj);
    let dec_conj = ctx.decrypt(&sk, &ct_conj);
    for i in 0..8 {
        let exp = slots1[i].conj();
        assert!(dec_conj[i].sub(exp).norm_sq() < 1e-10);
    }

    let ct_mul_unscaled = ctx.mul_no_rescale(&ct1, &ct2, &rk);
    let (ctx_rescaled, ct_rescaled) = ctx.rescale_drop_limb(&ct_mul_unscaled);
    assert_eq!(ctx_rescaled.basis.num_limbs(), 2);
    assert!((ct_rescaled.scale - scale).abs() < 1e-3);

    let dec_mul = ctx_rescaled.decrypt(&sk, &ct_rescaled);
    for i in 0..8 {
        let exp = slots1[i].mul(slots2[i]);
        let err_sq = dec_mul[i].sub(exp).norm_sq();
        assert!(
            err_sq < 1e-8,
            "CKKS rescaled mul slot {} mismatch: got {:?}, expected {:?}",
            i,
            dec_mul[i],
            exp
        );
    }
}
