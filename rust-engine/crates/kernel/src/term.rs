//! `Term` — deep-embedded AST of 213.
//!
//! Mirror of `lean/E213/Kernel/Term.lean`:
//!
//! ```lean
//! inductive Term : Type
//!   | zero | succ : Term → Term
//!   | add  : Term → Term → Term
//!   | mul  : Term → Term → Term
//! ```
//!
//! `eval : Term → ℕ` evaluates by structural recursion.  Carrier:
//! `BigUint` (no overflow).
//!
//! Lean citation: `E213.Kernel.Term.eval`, `Term.equiv`.

use num_bigint::BigUint;
use num_traits::Zero;

#[derive(Clone, Eq, PartialEq, Debug)]
pub enum Term {
    Zero,
    Succ(Box<Term>),
    Add(Box<Term>, Box<Term>),
    Mul(Box<Term>, Box<Term>),
}

// Names `add`/`mul` mirror Lean inductive cases, not std::ops traits.
#[allow(clippy::should_implement_trait)]
impl Term {
    /// `eval : Term → ℕ`.  Lean: `E213.Kernel.Term.eval`.
    pub fn eval(&self) -> BigUint {
        match self {
            Term::Zero          => BigUint::zero(),
            Term::Succ(t)       => t.eval() + 1u32,
            Term::Add(a, b)     => a.eval() + b.eval(),
            Term::Mul(a, b)     => a.eval() * b.eval(),
        }
    }

    /// `equiv` returns Bool — Lean: `E213.Kernel.Term.equiv`.
    pub fn equiv(a: &Term, b: &Term) -> bool {
        a.eval() == b.eval()
    }

    /// Convenience: build from a Rust `u64`.  Not a Lean primitive;
    /// this is a *constructor* for tests.  Decomposes via `succ`.
    pub fn from_nat(mut n: u64) -> Term {
        let mut t = Term::Zero;
        while n > 0 {
            t = Term::Succ(Box::new(t));
            n -= 1;
        }
        t
    }

    pub fn add(a: Term, b: Term) -> Term { Term::Add(Box::new(a), Box::new(b)) }
    pub fn mul(a: Term, b: Term) -> Term { Term::Mul(Box::new(a), Box::new(b)) }
    pub fn succ(t: Term) -> Term { Term::Succ(Box::new(t)) }
}

// 213 standard constants (mirror Term.nS / nT / d / c).
pub fn n_s() -> Term { Term::from_nat(3) }   // 3
pub fn n_t() -> Term { Term::from_nat(2) }   // 2
pub fn d()   -> Term { Term::from_nat(5) }   // 5
pub fn c()   -> Term { Term::from_nat(2) }   // 2

#[cfg(test)]
mod tests {
    use super::*;
    #[test] fn eval_constants() {
        assert_eq!(n_s().eval(), 3u32.into());
        assert_eq!(n_t().eval(), 2u32.into());
        assert_eq!(d().eval(),   5u32.into());
    }
    #[test] fn equiv_via_eval() {
        let three_a = Term::Add(Box::new(n_t()), Box::new(Term::from_nat(1)));
        assert!(Term::equiv(&three_a, &n_s()));
    }
}
