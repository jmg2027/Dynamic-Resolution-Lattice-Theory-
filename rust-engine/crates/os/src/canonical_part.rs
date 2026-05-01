//! Canonical (3, 2) split — derived from `Atomic 5` + canonical
//! partition.  Mirrors `lean/E213/OS/PairForcing.lean`
//! (`atomic_23_iff_five`) plus `Atomicity.canonical_partition`.

use crate::atomicity::{canonical_partition_holds, is_atomic};

/// Number of S-side vertices (one closure of size 3).
pub const N_S: u64 = 3;

/// Number of T-side vertices (one pair of size 2).
pub const N_T: u64 = 2;

/// Total: d = N_S + N_T = 5 (atomic).
pub const D: u64 = 5;

/// `canonical_split () = (N_S, N_T) = (3, 2)`.
pub fn canonical_split() -> (u64, u64) { (N_S, N_T) }

/// Sanity: `D = N_S + N_T` and `D` is `Atomic`.
/// Mirrors the bridge between PairForcing and Atomicity.
pub fn canonical_split_consistent() -> bool {
    N_S + N_T == D && is_atomic(D) && canonical_partition_holds()
}

/// `(a, b) = (1, 1)` is the unique alive decomposition of d = 5.
/// Sanity check: closure_count = 1, pair_count = 1.
pub fn canonical_partition_witnesses() -> (u64, u64) {
    // From Lean: canonical_partition forces (a, b) = (1, 1).
    // (closure-count, pair-count) = (1, 1).
    (1, 1)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::atomicity::{decomp, is_alive};

    #[test] fn split_is_three_two() { assert_eq!(canonical_split(), (3, 2)); }
    #[test] fn d_is_five()           { assert_eq!(D, 5); }
    #[test] fn split_sums_to_d()     { assert_eq!(N_S + N_T, D); }

    #[test] fn split_consistent_overall() {
        assert!(canonical_split_consistent());
    }

    #[test] fn partition_witnesses_one_one() {
        let (k_closure, k_pair) = canonical_partition_witnesses();
        assert_eq!((k_closure, k_pair), (1, 1));
        // Confirm the witness actually decomposes 5 with alive parts.
        assert!(decomp(D, k_closure, k_pair) && is_alive(k_closure, k_pair));
    }
}
