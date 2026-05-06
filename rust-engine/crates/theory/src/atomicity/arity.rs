//! Arity forcing + Pigeonhole.
//!
//! Mirrors `lean/E213/OS/{ArityForcing, ArityForcingGeneral,
//! Pigeonhole}.lean`.  Pigeonhole is the workhorse: when N < k, every
//! function `Fin k → Fin N` has a collision.  Arity forcing applies
//! this to a relation/closure that would require an injection of
//! arity > N into N atoms.

/// Lean: `Pigeonhole.no_inj_lt` (existence form) — for N < k, every
/// `g : Fin k → Fin N` has `i ≠ j` with `g i = g j`.
///
/// Returns the first such collision, or `None` if N ≥ k or `g` is
/// somehow injective (the theorem says when N < k that's impossible).
pub fn find_collision<F: Fn(u64) -> u64>(
    n: u64, k: u64, g: &F,
) -> Option<(u64, u64)> {
    if k <= 1 { return None; }
    for i in 0..k {
        for j in (i + 1)..k {
            if g(i) % n.max(1) == g(j) % n.max(1) {
                return Some((i, j));
            }
        }
    }
    None
}

/// Stronger form: when N < k, *every* g must collide.  Sample a
/// finite set of g and confirm.  The Lean theorem is universal; this
/// is a *local witness* that the local property holds.
pub fn pigeonhole_holds_universal_sample(n: u64, k: u64) -> bool {
    if n >= k { return true; }
    // Sample 8 deterministic g: g_s(i) = (i * s + s) mod n.
    for seed in 1u64..=8 {
        let g = |i: u64| (i.wrapping_mul(seed).wrapping_add(seed)) % n.max(1);
        if find_collision(n, k, &g).is_none() { return false; }
    }
    true
}

/// Lean: `ArityForcing.reachable3_only_object` — in the inductive
/// `Reachable3` predicate over `Raw3`, only the base constructor
/// `obj` is reachable; `rel3 x y z` is never reachable.  Mirror as
/// a Boolean classifier: an arity-3 relation cannot be inhabited.
///
/// Encoding: `Reachable3` distinguishes `obj` (always reachable) from
/// `rel3 _ _ _` (never reachable).  Returns `true` iff the value tag
/// is `Obj`.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Raw3Tag { Obj, Rel3 }

pub fn reachable3(t: Raw3Tag) -> bool { matches!(t, Raw3Tag::Obj) }

/// Generalized form (Lean: `ArityForcingGeneral.reachable_base_only`):
/// for k > N, no `rel_k` constructor is reachable.
pub fn reachable_base_only(n: u64, k: u64) -> bool { n < k }
