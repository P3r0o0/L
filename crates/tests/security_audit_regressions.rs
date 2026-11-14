use std::panic::{catch_unwind, AssertUnwindSafe};

use lwe::distributions::CenteredBinomial;
use lwe::estimator::SecurityReport;
use lwe::fhe::bfv::{BFVContext, BFVParams, RelinKey};
use lwe::fhe::bgv::BGVContext;
use lwe::fhe::ckks::{CKKSContext, Complex64};
use lwe::fhe::rns::generate_aux_basis;
use lwe::fhe::rns_bfv::RnsBFVContext;
use lwe::lwe::kem::ModKEMContext;
use lwe::lwe::math::{
    is_gadget_covering, is_prime_u64, sample_ternary_i64, sample_ternary_mod_q, BarrettModulus,
};
use lwe::lwe::ntt::is_primitive_2nth_root;
use lwe::lwe::pke::{ModPKEContext, ModPKEParams};
use lwe::lwe::poly::Polynomial;
use lwe::lwe::sample::LweSample;
use lwe::zkp::mod_nizk::{ModZKPParams, ModZKPWitness};
use lwe::zkp::nizk::{ZKPParams, ZKPWitness};
use rand::rngs::StdRng;
use rand::SeedableRng;

fn assert_panics<F: FnOnce() -> R, R>(f: F, context: &str) {
    let res = catch_unwind(AssertUnwindSafe(f));
    assert!(res.is_err(), "Expected panic for: {context}");
}

#[test]
fn test_vuln01_ckks_noise_flooding_mitigates_error_leakage() {
    let n = 8usize;
    let moduli = generate_aux_basis(n, &[], 2).moduli;
    let ctx = CKKSContext::new(n, moduli);
    let mut rng = StdRng::seed_from_u64(0xC1CC_5F10_0D01);

    let (sk, pk) = ctx.keygen_with_rng(&mut rng);
    let scale = (1u64 << 40) as f64;
    let inputs = vec![
        Complex64::new(1.25, -0.5),
        Complex64::new(-3.75, 2.125),
        Complex64::new(0.0, 1.0),
        Complex64::new(4.5, -1.5),
    ];

    let ct = ctx.encrypt_with_rng(&mut rng, &pk, &inputs, scale);
    let raw = ctx.decrypt(&sk, &ct);
    let flooded = ctx.decrypt_with_noise_flooding_and_rng(&mut rng, &sk, &ct, 20);

    let mut max_diff_from_raw = 0.0f64;
    for i in 0..inputs.len() {
        let err_re = (flooded[i].re - inputs[i].re).abs();
        let err_im = (flooded[i].im - inputs[i].im).abs();
        assert!(
            err_re < 1e-4 && err_im < 1e-4,
            "Flooded CKKS slot {i} lost excessive precision: ({err_re}, {err_im})"
        );
        let diff = (flooded[i].re - raw[i].re)
            .hypot(flooded[i].im - raw[i].im);
        if diff > max_diff_from_raw {
            max_diff_from_raw = diff;
        }
    }
    assert!(
        max_diff_from_raw > 1e-9,
        "Noise flooding must perturb raw approximate decryption to mask LWE error"
    );

    assert_panics(
        || ctx.decrypt_with_noise_flooding_and_rng(&mut rng, &sk, &ct, 0),
        "CKKS noise flooding with flood_bits == 0",
    );
    assert_panics(
        || ctx.decrypt_with_noise_flooding_and_rng(&mut rng, &sk, &ct, 61),
        "CKKS noise flooding with flood_bits > 60",
    );
}

#[test]
fn test_vuln02_barrett_div_rem_and_constant_time_ternary() {
    let moduli = [2u64, 3, 17, 97, 3329, 65537, (1u64 << 62) - 57];
    for &q in &moduli {
        let barrett = BarrettModulus::new(q);
        let edge_cases = [
            0u64,
            1,
            2,
            q - 1,
            q,
            q + 1,
            2 * q - 1,
            2 * q,
            2 * q + 1,
            (1u64 << 32) + 12345,
            u64::MAX - q,
            u64::MAX - 1,
            u64::MAX,
        ];
        for &x in &edge_cases {
            assert_eq!(
                barrett.div_rem_u64(x),
                (x / q, x % q),
                "BarrettModulus::div_rem_u64 mismatch for x={x}, q={q}"
            );
        }
    }

    let mut rng = StdRng::seed_from_u64(0x7E2A_A123);
    let q = 3329u64;
    let mut counts = [0usize; 3];
    for _ in 0..9000 {
        let v = sample_ternary_mod_q(&mut rng, q);
        if v == 0 {
            counts[0] += 1;
        } else if v == 1 {
            counts[1] += 1;
        } else if v == q - 1 {
            counts[2] += 1;
        } else {
            panic!("Non-ternary element mod q sampled: {v}");
        }

        let s = sample_ternary_i64(&mut rng);
        assert!(s == -1 || s == 0 || s == 1, "Non-ternary i64 sampled: {s}");
    }
    for (idx, &c) in counts.iter().enumerate() {
        assert!(
            (2750..=3250).contains(&c),
            "Unexpected ternary bucket {idx} count: {c}"
        );
    }
}

#[test]
fn test_vuln03_floor_delta_modpke_vs_bfv_rounding_margin() {
    let psi = ModPKEParams::find_psi(2, 101);
    let pke = ModPKEContext::new(1, 2, 101, 30, psi);
    let mut rng = StdRng::seed_from_u64(0xBF70_0101);
    let (sk, pk) = pke.keygen_with_rng(&mut rng);

    let pt = Polynomial::new(vec![29, 28]);
    let zero_vec = vec![Polynomial::zero(2)];
    let zero_poly = Polynomial::zero(2);
    let ct = pke.encrypt_with_randomness(&pk, &pt, &zero_vec, &zero_vec, &zero_poly);
    assert_eq!(pke.decrypt(&sk, &ct), pt);

    assert_panics(
        || BFVParams::new(2, 101, 30),
        "BFVParams::new must reject parameters where 2*(q%t)*(t-1) >= q",
    );
    assert_panics(
        || RnsBFVContext::new(2, vec![101], 30),
        "RnsBFVContext::new must reject parameters where 2*(Q%t)*(t-1) >= Q",
    );
    let sample = LweSample::new(vec![vec![0u64; 4]], vec![0u64]);
    assert_panics(
        || sample.encrypt_messages(&[29], 30, 101),
        "LweSample::encrypt_messages must reject parameters where 2*(q%t)*(t-1) >= q",
    );
}

#[test]
fn test_vuln04_zkp_strict_bounds_and_verifier_enforcement() {
    assert_panics(
        || ZKPParams::new(4, 3329, 100, 100),
        "ZKPParams::new with bound_b == beta",
    );
    assert_panics(
        || ModZKPParams::new(2, 2, 4, 97, 20, 20, 33),
        "ModZKPParams::new with bound_b == beta",
    );

    let zkp = ZKPParams::new(4, 3329, 200, 3);
    let a_poly = Polynomial::zero(4);
    let witness = ZKPWitness {
        s: Polynomial::new(vec![1, 0, 0, 0]),
        e: Polynomial::zero(4),
    };
    let mut rng = StdRng::seed_from_u64(0x2B04_0001);
    assert_panics(
        || zkp.prove_with_rng(&mut rng, &a_poly, &witness),
        "ZKPParams::prove_with_rng when beta < n * ||w||_inf",
    );

    let mut mod_zkp = ModZKPParams::new(1, 1, 4, 97, 30, 8, 33);
    let a_mat = vec![vec![Polynomial::new(vec![1, 2, 3, 4])]];
    let s_vec = vec![Polynomial::new(vec![1, 0, 96, 0])];
    let e_vec = vec![Polynomial::new(vec![0, 1, 0, 96])];
    let mod_wit = ModZKPWitness { s: s_vec, e: e_vec };
    let (mod_pub, proof, _) = mod_zkp.prove_with_rng(&mut rng, &a_mat, &mod_wit);
    assert!(mod_zkp.verify(&mod_pub, &proof));

    let mut forged_params_hi = ModZKPParams::new(1, 1, 4, 97, 30, 8, 33);
    forged_params_hi.bound_b = 97 / 2;
    assert!(!forged_params_hi.verify(&mod_pub, &proof));

    mod_zkp.bound_b = mod_zkp.beta;
    assert!(!mod_zkp.verify(&mod_pub, &proof));
}

#[test]
fn test_vuln05_primality_u64_full_range_and_primitive_2nth_root() {
    assert!(!is_prime_u64(0));
    assert!(!is_prime_u64(1));
    assert!(is_prime_u64(2));
    assert!(is_prime_u64(3));
    assert!(!is_prime_u64(1u64 << 62));
    assert!(!is_prime_u64((1u64 << 62) + 1));
    assert!(is_prime_u64((1u64 << 63) - 25));
    assert!(is_prime_u64(u64::MAX - 58));
    assert!(!is_prime_u64(u64::MAX));

    assert!(!is_primitive_2nth_root(6, 3, 7));
    assert!(is_primitive_2nth_root(3, 3, 7));
    assert_panics(
        || ModPKEParams::new(1, 3, 7, 2, 6),
        "Non-primitive root psi=6 for n=3, q=7",
    );
    let valid_pke_params = ModPKEParams::new(1, 3, 7, 2, 3);
    assert_eq!(valid_pke_params.psi, 3);

    assert!(!is_primitive_2nth_root(14, 1, 15));
    assert_panics(
        || ModPKEParams::new(1, 1, 15, 2, 14),
        "Composite modulus q=15 in ModPKEParams::new",
    );
    assert_panics(
        || BFVParams::new_with_ntt(4, 15, 2, 2),
        "Composite modulus q=15 in BFVParams::new_with_ntt",
    );
}

#[test]
fn test_vuln06_gadget_completeness_and_deserialization_validation() {
    assert!(!is_gadget_covering(16, 4, 65537));
    assert!(is_gadget_covering(16, 5, 65537));
    assert!(is_gadget_covering(u64::MAX, 2, u64::MAX));

    let psi = ModPKEParams::find_psi(8, 65537);
    let bfv = BFVContext::new_with_ntt(8, 65537, 17, psi);
    let mut rng = StdRng::seed_from_u64(0x6AD6_E706);
    let (sk, _) = bfv.keygen_with_rng(&mut rng);

    assert_panics(
        || bfv.keygen_relin_with_rng(&mut rng, &sk, 16, 4),
        "BFV keygen_relin with incomplete gadget 16^4 < 65537",
    );
    let rk_valid = bfv.keygen_relin_with_rng(&mut rng, &sk, 16, 5);
    let rk_bytes = rk_valid.to_bytes();
    assert!(RelinKey::from_bytes(&rk_bytes, 8, 65537).is_some());

    let mut tampered = rk_bytes.clone();
    tampered[0..8].copy_from_slice(&4u64.to_le_bytes());
    assert!(
        RelinKey::from_bytes(&tampered, 8, 65537).is_none(),
        "RelinKey::from_bytes must reject incomplete gadget parameters"
    );

    let rns_bfv = RnsBFVContext::new(8, vec![65537], 17);
    let (rns_sk, _) = rns_bfv.keygen_with_rng(&mut rng);
    assert_panics(
        || rns_bfv.keygen_relin_with_rng(&mut rng, &rns_sk, 16, 4),
        "RnsBFV keygen_relin with incomplete gadget 16^4 < 65537",
    );

    let bgv = BGVContext::new(8, vec![65537], 17);
    let (bgv_sk, _) = bgv.keygen_with_rng(&mut rng);
    assert_panics(
        || bgv.keygen_relin_with_rng(&mut rng, &bgv_sk, 16, 4),
        "BGV keygen_relin with incomplete gadget 16^4 < 65537",
    );

    let ckks = CKKSContext::new(8, vec![65537, 114689]);
    let (ckks_sk, _) = ckks.keygen_with_rng(&mut rng);
    assert_panics(
        || ckks.keygen_relin_with_rng(&mut rng, &ckks_sk, 16, 4),
        "CKKS keygen_relin with incomplete gadget 16^4 < 65537",
    );
}

#[test]
fn test_vuln07_08_09_cbd_bound_d4f_report_and_kem_malformed_pk() {
    let mut rng = StdRng::seed_from_u64(0xCBD0_7890);
    let cbd_bad = CenteredBinomial { eta: 17 };
    assert_panics(
        || cbd_bad.sample_cbd_elem(&mut rng, 17),
        "CenteredBinomial must reject eta >= q",
    );
    let cbd_ok = CenteredBinomial { eta: 16 };
    let sample = cbd_ok.sample_cbd_elem(&mut rng, 17);
    assert!(sample < 17);

    let p = ModPKEParams::preset_standard_128bit();
    let report = SecurityReport::evaluate_mod_pke(p.k, p.n, p.q, None, None, None);
    assert!(report.min_d4f_classical_bits > 0.0);
    assert!(
        report.min_d4f_classical_bits <= report.min_classical_bits + 1e-9,
        "D4F classical bits ({}) must not exceed standard core-SVP classical bits ({})",
        report.min_d4f_classical_bits,
        report.min_classical_bits
    );

    let kem = ModKEMContext::preset_toy_zero_failure();
    let (_, mut pk) = kem.keygen_with_rng(&mut rng);
    pk.t[0].coeffs[0] = kem.pke.params.q;
    assert_panics(
        || kem.encaps_with_rng(&mut rng, &pk),
        "ModKEMContext::encaps_with_rng must reject non-canonical public keys",
    );
}
