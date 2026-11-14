use crate::distributions::ErrorDistribution;
use crate::lwe::math::sub_mod;
use crate::lwe::poly::Polynomial;
use crate::params::LweParams;
use alloc::vec::Vec;
use rand::Rng;

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct CenteredBinomial {
    pub eta: usize,
}

pub type DiscreteGaussian = CenteredBinomial;

impl CenteredBinomial {
    #[inline]
    pub fn sample_cbd_elem<R: Rng + ?Sized>(&self, rng: &mut R, q: u64) -> u64 {
        assert!(
            q >= 2 && (self.eta as u64) < q,
            "CBD parameter eta must be strictly less than modulus q (with q >= 2)"
        );
        let mut a = 0u64;
        let mut b = 0u64;
        let mut remaining = self.eta;
        while remaining > 0 {
            let chunk = remaining.min(32);
            let bits = rng.next_u64();
            let mask = if chunk == 32 {
                u32::MAX as u64
            } else {
                (1u64 << chunk) - 1
            };
            a += (bits & mask).count_ones() as u64;
            b += ((bits >> 32) & mask).count_ones() as u64;
            remaining -= chunk;
        }
        sub_mod(a, b, q)
    }

    pub fn sample_with_rng<R: Rng + ?Sized>(&self, rng: &mut R, params: &LweParams) -> Vec<u64> {
        let mut error = Vec::with_capacity(params.m);
        for _ in 0..params.m {
            error.push(self.sample_cbd_elem(rng, params.q));
        }
        error
    }

    pub fn sample_poly_with_rng<R: Rng + ?Sized>(
        &self,
        rng: &mut R,
        n: usize,
        q: u64,
    ) -> Polynomial {
        let mut coeffs = Vec::with_capacity(n);
        for _ in 0..n {
            coeffs.push(self.sample_cbd_elem(rng, q));
        }
        Polynomial::new(coeffs)
    }

    #[cfg(feature = "std")]
    pub fn sample_poly(&self, n: usize, q: u64) -> Polynomial {
        let mut rng = rand::thread_rng();
        self.sample_poly_with_rng(&mut rng, n, q)
    }
}

impl ErrorDistribution for CenteredBinomial {
    fn sample_with_rng(&self, rng: &mut dyn rand::RngCore, params: &LweParams) -> Vec<u64> {
        CenteredBinomial::sample_with_rng(self, rng, params)
    }
}
