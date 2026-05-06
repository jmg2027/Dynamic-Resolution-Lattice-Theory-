//! 5 starter `RewriteRule` impls citing `Kernel/MonomialAxioms.lean`.

use super::{Expr, RewriteRule};
use num_bigint::BigUint;

fn x()       -> Expr { Expr::X }
fn y()       -> Expr { Expr::Y }
fn k(n: u32) -> Expr { Expr::Const(BigUint::from(n)) }
fn mul(a: Expr, b: Expr) -> Expr { Expr::Mul(Box::new(a), Box::new(b)) }
fn pow(a: Expr, n: u64)  -> Expr { Expr::Pow(Box::new(a), n) }

/// Lean: `MonomialAxioms.ns_mul_nt_eq_six` — `NS · NT = 6`.
pub struct NsMulNtEqSix;
impl RewriteRule for NsMulNtEqSix {
    const LEAN_THM: &'static str = "E213.Term.MonomialAxioms.ns_mul_nt_eq_six";
    fn lhs() -> Expr { mul(x(), y()) }
    fn rhs() -> Expr { k(6) }
}

/// Lean: `MonomialAxioms.mul_comm_ns_nt` — `NS · NT = NT · NS`.
pub struct MulCommNsNt;
impl RewriteRule for MulCommNsNt {
    const LEAN_THM: &'static str = "E213.Term.MonomialAxioms.mul_comm_ns_nt";
    fn lhs() -> Expr { mul(x(), y()) }
    fn rhs() -> Expr { mul(y(), x()) }
}

/// Lean: `MonomialAxioms.ns_sq_eq_9` — `NS² = 9`.
pub struct NsSqEq9;
impl RewriteRule for NsSqEq9 {
    const LEAN_THM: &'static str = "E213.Term.MonomialAxioms.ns_sq_eq_9";
    fn lhs() -> Expr { pow(x(), 2) }
    fn rhs() -> Expr { k(9) }
}

/// Lean: `MonomialAxioms.nt_sq_eq_4` — `NT² = 4`.
pub struct NtSqEq4;
impl RewriteRule for NtSqEq4 {
    const LEAN_THM: &'static str = "E213.Term.MonomialAxioms.nt_sq_eq_4";
    fn lhs() -> Expr { pow(y(), 2) }
    fn rhs() -> Expr { k(4) }
}

/// Lean: `MonomialAxioms.d_sq_eq_25` — `d · d = 25`.
pub struct DSqEq25;
impl RewriteRule for DSqEq25 {
    const LEAN_THM: &'static str = "E213.Term.MonomialAxioms.d_sq_eq_25";
    fn lhs() -> Expr { mul(k(5), k(5)) }
    fn rhs() -> Expr { k(25) }
}
