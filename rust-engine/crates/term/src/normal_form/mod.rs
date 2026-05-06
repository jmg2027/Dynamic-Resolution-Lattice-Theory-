//! NormalForm — `coeff · x^p · y^q` Monomial form + Expr + RewriteRule.
//!
//! Decidability bridge: monomials compare by tuple equality.  When
//! lhs and rhs of a rewrite rule do not coincide structurally, fall
//! back to evaluation at (x, y) = (NS, NT) = (3, 2) — same shape
//! Lean's `rfl` proofs take.
//!
//! Lean theorems live in `lean/E213/Kernel/MonomialAxioms.lean`
//! (each 0-axiom by `rfl` on concrete values).

use num_bigint::BigUint;

pub mod monomial;
pub mod rules;

pub use monomial::Monomial;

#[derive(Clone, Debug)]
pub enum Expr {
    Const(BigUint),
    X, Y,
    Mul(Box<Expr>, Box<Expr>),
    Pow(Box<Expr>, u64),
}

pub fn normalize(e: &Expr) -> Monomial {
    match e {
        Expr::Const(c)  => Monomial::from_const(c.clone()),
        Expr::X         => Monomial::x(),
        Expr::Y         => Monomial::y(),
        Expr::Mul(a, b) => normalize(a).mul(&normalize(b)),
        Expr::Pow(a, n) => normalize(a).pow(*n),
    }
}

pub trait RewriteRule {
    const LEAN_THM: &'static str;
    fn lhs() -> Expr;
    fn rhs() -> Expr;

    /// Validate at (x, y) = (NS, NT) = (3, 2) — values where the
    /// cited Lean theorem is `rfl`-closed.
    fn validate() -> bool {
        let x = BigUint::from(3u32); let y = BigUint::from(2u32);
        normalize(&Self::lhs()).eval_at(&x, &y)
            == normalize(&Self::rhs()).eval_at(&x, &y)
    }
}
