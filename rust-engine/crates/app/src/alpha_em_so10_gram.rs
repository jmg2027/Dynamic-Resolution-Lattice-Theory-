//! α_em SO(10) tail + Gram self-energy — Rust mirrors of Lean defs.
//!
//! Mirrors:
//!   `lean/E213/Physics/AlphaEMSO10.lean`           (add_so10_tail, inv_*_so10)
//!   `lean/E213/Physics/AlphaEMGramSelfEnergy.lean` (add_gram_self_energy,
//!                                                    inv_*_aug)
//!
//! All ℕ-pair arithmetic, no Q-algebra abstraction.  Verified
//! identical to Lean #eval at registered N values via the
//! `lean-rust-diff` tool.

use crate::alpha_em::{inv_lower_tight, inv_full_upper};
use crate::basel::{s_partial, upper, Q};
use num_bigint::BigUint;

fn nat(n: u64) -> BigUint { BigUint::from(n) }

/// `add_so10_tail p u = (p.1·(4500·u.1) + 49·u.2·p.2, p.2·(4500·u.1))`.
/// Mirrors `AlphaEMSO10.add_so10_tail`.  Adds the SO(10)-level Dyson
/// tail term `α_GUT · (1/(NS+1) + 1/(NS²·d)) = α_GUT · 49/180`
/// (with α_GUT = 1/(25·ζ(2)), so the tail term = 49/(4500·ζ(2)),
/// represented as 49·u.2/(4500·u.1) where u brackets ζ(2)).
pub fn add_so10_tail(p: &Q, u: &Q) -> Q {
    // Lean: (p.1 * (4500 * u.1) + 49 * u.2 * p.2, p.2 * (4500 * u.1))
    // Lean .1 = num, .2 = den; Rust .0 = num, .1 = den.
    let scale = nat(4500u64) * &u.0;
    let term_num = nat(49u64) * &u.1 * &p.1;
    let new_num = &p.0 * &scale + &term_num;
    let new_den = &p.1 * &scale;
    (new_num, new_den)
}

/// `inv_lower_so10 N = add_so10_tail (inv_lower_tight N) (upper N)`.
pub fn inv_lower_so10(n: u64) -> Q {
    add_so10_tail(&inv_lower_tight(n), &upper(n))
}

/// `inv_upper_so10 N = add_so10_tail (inv_full_upper N) (S N)`.
pub fn inv_upper_so10(n: u64) -> Q {
    add_so10_tail(&inv_full_upper(n), &s_partial(n))
}

/// `alpha_em_sq_over_d_sq_approx = (213, 10⁸)`.  Matches Lean
/// `AlphaEMGramSelfEnergy.alpha_em_sq_over_d_sq_approx`.
pub fn alpha_em_sq_over_d_sq_approx() -> Q {
    (nat(213u64), nat(100_000_000u64))
}

/// `add_gram_self_energy p = (p.1·10⁸ + 213·p.2, p.2·10⁸)`.
/// Mirrors `AlphaEMGramSelfEnergy.add_gram_self_energy`.
pub fn add_gram_self_energy(p: &Q) -> Q {
    let big = nat(100_000_000u64);
    let new_num = &p.0 * &big + nat(213u64) * &p.1;
    let new_den = &p.1 * &big;
    (new_num, new_den)
}

/// `inv_lower_aug N = add_gram_self_energy (inv_lower_so10 N)`.
pub fn inv_lower_aug(n: u64) -> Q {
    add_gram_self_energy(&inv_lower_so10(n))
}

/// `inv_upper_aug N = add_gram_self_energy (inv_upper_so10 N)`.
pub fn inv_upper_aug(n: u64) -> Q {
    add_gram_self_energy(&inv_upper_so10(n))
}
