//! `Compare` — Bool-valued ≤ and < on `Term`.
//!
//! Mirror of `lean/E213/Kernel/Compare.lean`:
//!
//! ```lean
//! def le_b (a b : Term) : Bool := Nat.ble (eval a) (eval b)
//! def lt_b (a b : Term) : Bool := Nat.ble (Nat.succ (eval a)) (eval b)
//! ```
//!
//! Lean citation: `E213.Kernel.Term.le_b`, `Term.lt_b`.

use crate::term::Term;

/// `le_b a b = (eval a ≤ eval b)`.
pub fn le_b(a: &Term, b: &Term) -> bool {
    a.eval() <= b.eval()
}

/// `lt_b a b = (eval a < eval b)`.
pub fn lt_b(a: &Term, b: &Term) -> bool {
    a.eval() < b.eval()
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::term::{n_s, n_t, d, c};

    /// Mirror of `Compare.nT_lt_nS : lt_b nT nS = true`.
    #[test] fn n_t_lt_n_s() { assert!(lt_b(&n_t(), &n_s())); }

    /// Mirror of `Compare.nS_lt_d : lt_b nS d = true`.
    #[test] fn n_s_lt_d()   { assert!(lt_b(&n_s(), &d())); }

    /// Mirror of `Compare.nT_le_c : le_b nT c = true`.
    #[test] fn n_t_le_c()   { assert!(le_b(&n_t(), &c())); }
}
