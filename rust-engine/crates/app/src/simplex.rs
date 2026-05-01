//! 4-simplex with (3, 2) partition.
//!
//! Mirror of `lean/E213/App/Simplex.lean`.  V_A = {0, 1, 2}, V_B = {3, 4}.
//! `BlockPair` classifier produces 6 equivalence classes summing to
//! 25 = d² (3 + 6 + 6 + 6 + 2 + 2).  Aut = S_3 × S_2 acts on classes.

/// Lean: `Simplex.isA i := i.val < 3`.
pub fn is_a(i: u8) -> bool { i < 3 }

/// Lean: `Simplex.BlockPair` — 6 classes.
#[derive(Clone, Copy, Eq, PartialEq, Debug)]
pub enum BlockPair {
    AAdiag, AAoff, AB, BA, BBdiag, BBoff,
}

/// Lean: `Simplex.classify i j`.
pub fn classify(i: u8, j: u8) -> BlockPair {
    use BlockPair::*;
    match (is_a(i), is_a(j)) {
        (true,  true)  => if i == j { AAdiag } else { AAoff },
        (true,  false) => AB,
        (false, true)  => BA,
        (false, false) => if i == j { BBdiag } else { BBoff },
    }
}

/// Class size counts — must sum to 25 = d² (Lean: comment in
/// Simplex.lean: "3 + 6 + 6 + 6 + 2 + 2 = 25 = d²").
pub fn class_count(c: BlockPair) -> u8 {
    use BlockPair::*;
    match c { AAdiag => 3, AAoff => 6, AB => 6, BA => 6, BBdiag => 2, BBoff => 2 }
}

/// `Σ class_count = 25`.
pub fn class_counts_sum_to_25() -> bool {
    use BlockPair::*;
    [AAdiag, AAoff, AB, BA, BBdiag, BBoff]
        .iter().map(|c| class_count(*c) as u32).sum::<u32>() == 25
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test] fn is_a_partition() {
        for i in 0..3 { assert!(is_a(i)); }
        for i in 3..5 { assert!(!is_a(i)); }
    }

    #[test] fn classify_diag() {
        assert_eq!(classify(0, 0), BlockPair::AAdiag);
        assert_eq!(classify(3, 3), BlockPair::BBdiag);
    }

    #[test] fn classify_offdiag() {
        assert_eq!(classify(0, 1), BlockPair::AAoff);
        assert_eq!(classify(0, 3), BlockPair::AB);
        assert_eq!(classify(3, 0), BlockPair::BA);
        assert_eq!(classify(3, 4), BlockPair::BBoff);
    }

    #[test] fn class_sum_is_d_squared() {
        assert!(class_counts_sum_to_25());
    }
}
