//! Wallis / Leibniz π brackets — 213-internal rational approximations.
//!
//! Mirrors `lean/E213/Research/Real213CutTrig.lean` (`leibnizPiPartial`).
//!
//! Leibniz series: π/4 = 1 − 1/3 + 1/5 − 1/7 + 1/9 − ... = Σ (−1)^i/(2i+1)
//!
//! Alternating-series bound: with S_n = Σ_{i<n} (−1)^i/(2i+1),
//!   • S_{2k}   ≤ π/4 ≤ S_{2k+1}   (last term negative → under, positive → over)
//!   • |S_n − π/4| ≤ |a_n| = 1/(2n+1)  (next-term magnitude)
//!
//! `pi_quarter_bracket(n)` returns (lo, hi) Q-pair such that
//!   lo ≤ π/4 ≤ hi  and  hi − lo ≤ 2/(2n+1).
//!
//! Multiplied by 4: `pi_bracket(n)` for π itself.
//! Reciprocal: if `lo ≤ π ≤ hi` then `1/hi ≤ 1/π ≤ 1/lo`.

use crate::basel::Q;
use num_bigint::BigUint;

fn nat(n: u64) -> BigUint { BigUint::from(n) }

/// Leibniz partial sum S_n = Σ_{i<n} (−1)^i / (2i+1).
/// Returns (sign_pos, |Q|).  sign_pos = true means ≥ 0.
fn leibniz_partial_signed(n: u64) -> (bool, Q) {
    if n == 0 { return (true, (nat(0), nat(1))); }
    let mut num = BigUint::from(0u32);
    let mut den = BigUint::from(1u32);
    let mut sign_pos = true;
    for i in 0..n {
        let term_den = nat(2 * i + 1);
        let new_den = &den * &term_den;
        let scaled_old = &num * &term_den;
        let scaled_term = den.clone();
        if i % 2 == 0 {
            num = scaled_old + scaled_term;
        } else if scaled_old >= scaled_term {
            num = scaled_old - scaled_term;
        } else {
            num = scaled_term - scaled_old;
            sign_pos = !sign_pos;
        }
        den = new_den;
    }
    (sign_pos, (num, den))
}

/// π/4 bracket: returns (lo, hi) such that lo ≤ π/4 ≤ hi.
/// Width ≤ 2/(2n+1).  Use n ≥ 50 for ~ppm precision.
pub fn pi_quarter_bracket(n: u64) -> (Q, Q) {
    let n_even = if n % 2 == 0 { n } else { n + 1 };
    let n_odd = n_even + 1;
    let (s_even_pos, s_even) = leibniz_partial_signed(n_even);
    let (s_odd_pos, s_odd) = leibniz_partial_signed(n_odd);
    debug_assert!(s_even_pos && s_odd_pos);
    (s_even, s_odd)
}

/// π bracket: 4·(π/4 bracket).
pub fn pi_bracket(n: u64) -> (Q, Q) {
    let (lo, hi) = pi_quarter_bracket(n);
    ((nat(4) * lo.0, lo.1), (nat(4) * hi.0, hi.1))
}

/// 1/π bracket: reciprocal of π bracket.
/// If 0 < lo ≤ π ≤ hi, then 1/hi ≤ 1/π ≤ 1/lo.
pub fn inv_pi_bracket(n: u64) -> (Q, Q) {
    let (lo, hi) = pi_bracket(n);
    ((hi.1, hi.0), (lo.1, lo.0))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test] fn pi_bracket_contains_pi_at_n50() {
        let (lo, hi) = pi_bracket(50);
        let pi_known: Q = (nat(31415926535u64), nat(10_000_000_000u64));
        let lo_le = &lo.0 * &pi_known.1 <= &pi_known.0 * &lo.1;
        let pi_le_hi = &pi_known.0 * &hi.1 <= &hi.0 * &pi_known.1;
        assert!(lo_le && pi_le_hi);
    }

    #[test] fn inv_pi_bracket_contains_inv_pi() {
        let (lo, hi) = inv_pi_bracket(50);
        let target: Q = (nat(318_309_886_184u64), nat(10u64.pow(12)));
        let lo_le = &lo.0 * &target.1 <= &target.0 * &lo.1;
        let t_le_hi = &target.0 * &hi.1 <= &hi.0 * &target.1;
        assert!(lo_le && t_le_hi);
    }
}
