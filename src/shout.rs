#![allow(unused_variables)]
#![allow(dead_code)]
use ff::{Field, PrimeField};

use crate::{
  errors::SpartanError,
  polys::{eq::EqPolynomial, multilinear::MultilinearPolynomial},
  provider::VestaHyraxEngine,
  traits::{Engine, transcript::TranscriptEngineTrait},
};

const NUM_BITS_ADDR: usize = 32;

fn raf_to_bits(raf: &[u32]) -> Vec<bool> {
  raf
    .iter()
    .map(|raf| {
      let mut bits = [false; NUM_BITS_ADDR];
      for i in 0..NUM_BITS_ADDR {
        bits[i] = (raf & (1 << i)) != 0;
      }
      bits
    })
    .flatten()
    .collect()
}

fn get_limb<const D: usize>(ra_bits: &[bool], limb_id: usize, cycle: usize) -> u32 {
  let start = NUM_BITS_ADDR * cycle;
  let end = start + NUM_BITS_ADDR / D * (limb_id + 1);
  ra_bits[start..end]
    .iter()
    .fold(0, |acc, bit| acc * 2 + if *bit { 1 } else { 0 })
}

// f(j; i, tau_i) = ra_i(\tau_i, j)
fn eval_ra<const D: usize, F: PrimeField>(
  ra_bits: &[bool],
  chal: &[F],
  limb_id: usize,
) -> MultilinearPolynomial<F> {
  let eq_tau = EqPolynomial::new(chal.to_vec()).evals();
  let t = ra_bits.len() / NUM_BITS_ADDR;
  let list = (0..t)
    .map(|j| {
      let limb = get_limb::<D>(ra_bits, limb_id, j);
      eq_tau[limb as usize]
    })
    .collect();
  MultilinearPolynomial::new(list)
}

const D: usize = 4;
type F = halo2curves::pasta::Fp;

fn compute_prefix() -> Vec<MultilinearPolynomial<F>> {
  todo!()
}

struct ShoutAddress {
  raf_small: Vec<u32>,
  ra_limb: Vec<[u32; D]>,
  ra_bits: Vec<[bool; NUM_BITS_ADDR]>,
  t: usize,
}

fn merge_ra_acc(acc: &mut MultilinearPolynomial<F>, ra: &MultilinearPolynomial<F>) {
  acc
    .Z
    .iter_mut()
    .zip(ra.Z.iter())
    .for_each(|(acc_val, ra_val)| {
      *acc_val *= *ra_val;
    });
}

impl ShoutAddress {
  // f(j; i, cha_i) = ra_i(chal_i, j)
  fn make_binded_ra<F: PrimeField>(&self, limb_id: usize, chal: &[F]) -> MultilinearPolynomial<F> {
    let eq_tau = EqPolynomial::new(chal.to_vec()).evals();
    let list = self
      .ra_limb
      .iter()
      .map(|limbs| {
        let limb = limbs[limb_id];
        eq_tau[limb as usize]
      })
      .collect();
    MultilinearPolynomial::new(list)
  }

  // * Prefix_j(k_i) = ra_1(r_1, j) * ... * ra_{i-1}(r_{i-1}, j) * ra_i(k_i, j)
  // * Prefix_j(k1) = ra1(k1, j)
  // * Prefix_j(k2) = ra_1(tau_1, j) * ra_2(k2, j), only at limb 2 of address in cycle j, make it ra_1(tau_1, j)
  // * Prefix_j(k3) = ra_1(tau_1, j) * ra_2(tau_2, j) * ra_3(k3, j), only at limb 3 of address in cycle j, make it ra_1(tau_1, j) * ra_2(tau_2, j)
  // * O(T)
  fn compute_prefix(
    &self,
    limb_id: usize,
    binded_ra_accumulated: &MultilinearPolynomial<F>,
  ) -> Vec<MultilinearPolynomial<F>> {
    self
      .ra_limb
      .iter()
      .zip(binded_ra_accumulated.Z.iter())
      .map(|(limbs, binded_ra_val)| {
        let limb = limbs[limb_id];
        let mut list = vec![F::ZERO; self.t];
        list[limb as usize] = *binded_ra_val;
        MultilinearPolynomial::new(list)
      })
      .collect()
  }

  // Q_j(k1) = sum_{kRight} Val(k1, k_right) * ra_2(k_2, j) * ...
  // Q_j(k2) = sum_{kRight} Val(tau1, k2, k_right) * ra_3(k_3, j) * ra_4(k_4, j) * ...
  // To Init, Take Binded Val, at all k2 with limbs 2, 3, 4, ..., make them Val(k2)
  // * O(T * K^{1/d})
  fn compute_suffix_q(
    &self,
    limb_id: usize,
    binded_val: &MultilinearPolynomial<F>,
  ) -> Vec<MultilinearPolynomial<F>> {
    let limb_width = (NUM_BITS_ADDR / D) as u32;
    let limb_range = 1 << limb_width;
    (0..self.t)
      .map(|cycle| {
        let list = (0..limb_range)
          .into_iter()
          .map(|cur_limb| {
            let right_limbs = &self.ra_limb[cycle][limb_id + 1..];
            let full_k = cur_limb as u32
              + right_limbs
                .iter()
                .fold(0, |acc, limb| acc * limb_width + *limb);
            binded_val.Z[full_k as usize]
          })
          .collect();
        MultilinearPolynomial::new(list)
      })
      .collect()
  }
}

type E = VestaHyraxEngine;

fn prove_reading_checking_shout_sumcheck(
  address: &ShoutAddress,
  val: &MultilinearPolynomial<F>,
  r_cycle: &[F],
  transcript: &mut <E as Engine>::TE,
) -> Result<(), SpartanError> {
  let mut binded_ra_accumulated = MultilinearPolynomial::new(vec![F::ONE; address.t]);
  let mut binded_ra = Vec::with_capacity(D);

  let mut val = val.clone();

  let eq_r_cycle = EqPolynomial::new(r_cycle.to_vec()).evals();

  let num_rounds = NUM_BITS_ADDR / D;

  // first phase, over K
  for stage in 0..D {
    let poly_p = address.compute_prefix(stage, &binded_ra_accumulated);
    let poly_q = address.compute_suffix_q(stage, &mut val);
    for _round in 0..num_rounds {
      // * Squeeze
      _ = poly_p.iter().zip(poly_q.iter()).map(|(p, q)| {
        // * Eval f(0), f(2)
      });

      let chal: Vec<F> = vec![transcript.squeeze(b"chal").unwrap()];

      let ra = address.make_binded_ra(stage, &chal);
      merge_ra_acc(&mut binded_ra_accumulated, &ra);
      binded_ra.push(ra);

      // * Absorb
      // * Sum with eq(r_cycle, cycle)
    }
    // * Val Bind, par fire and forget
  }

  // second phase, over T
  todo!()
}
