//! Gap explorer — enumerate 213-pure ℚ quantities and rank by
//! proximity to a target.  Pure-ℚ = from {NS,NT,d,c} + chiral_dim
//! + b1_bipartite + α_GUT bracket via ×, ÷.  No floats.

use crate::basel::{s_partial, upper, Q};
use drlt_lens::{b1_bipartite, chiral_dim};
use num_bigint::BigUint;

pub fn nat(n: u64) -> BigUint { BigUint::from(n) }

/// |a − b| as ℚ pair.  Use `lt_q` to compare.
pub fn abs_diff(a: &Q, b: &Q) -> Q {
    let (l, r) = (&a.0 * &b.1, &b.0 * &a.1);
    let num = if l > r { l - r } else { r - l };
    (num, &a.1 * &b.1)
}

/// ℚ-pair `<` via cross-mul.
pub fn lt_q(p: &Q, q: &Q) -> bool { &p.0 * &q.1 < &q.0 * &p.1 }

pub fn decimal(q: &Q, scale: u32) -> String {
    let big = nat(10).pow(scale);
    let s = &q.0 * &big / &q.1;
    format!("{}.{:0>w$}", &s / &big, &s % &big, w = scale as usize)
}

fn dpow(p: u32) -> u64 { 5u64.pow(p) }

/// All DRLT-pure ℚ candidates.  Each label traces to its 213 origin.
pub fn candidates(n: u64) -> Vec<(String, Q)> {
    let mut v: Vec<(String, Q)> = Vec::new();
    let u = upper(n); let s = s_partial(n);
    let agut_lo: Q = (u.1.clone(), nat(25) * &u.0);
    let agut_hi: Q = (s.1.clone(), nat(25) * &s.0);
    let asq = (&agut_lo.0 * &agut_lo.0, &agut_lo.1 * &agut_lo.1);
    let acu = (&asq.0 * &agut_lo.0, &asq.1 * &agut_lo.1);

    v.push(("α_GUT (lo)".into(), agut_lo.clone()));
    v.push(("α_GUT (hi)".into(), agut_hi));
    v.push(("α_GUT² (lo)".into(), asq.clone()));
    v.push(("α_GUT³ (lo)".into(), acu.clone()));
    v.push(("(α_GUT/4)²".into(), (asq.0.clone(), &asq.1 * nat(16))));

    for &k in &[1u64, 2, 3, 4, 5, 6, 8, 10, 25] {
        for p in 2..=5u32 {
            v.push((format!("1/({}·d^{})", k, p), (nat(1), nat(k * dpow(p)))));
        }
    }
    for i in 0..=3u64 { for j in 0..=2u64 {
        let cd = chiral_dim(i, j);
        if cd == 0 { continue; }
        for p in 4..=6u32 {
            v.push((format!("chiral_dim({},{})/d^{}", i, j, p),
                (nat(cd), nat(dpow(p)))));
        }
    }}
    for nn in 2..=4u64 { for mm in 1..=3u64 { for c in 1..=3u64 {
        let b = b1_bipartite(nn, mm, c);
        if b == 0 { continue; }
        v.push((format!("b1_K({},{})c{}/d^4", nn, mm, c),
            (nat(b), nat(dpow(4)))));
    }}}
    for &k in &[1u64, 2, 3, 4, 5, 9, 25, 45] {
        for p in 0..=2u32 {
            v.push((format!("α_GUT/({}·d^{})", k, p),
                (agut_lo.0.clone(), &agut_lo.1 * nat(k * dpow(p)))));
        }
    }
    for &k in &[1u64, 2, 3, 5, 6, 9, 10, 25, 45] {
        v.push((format!("α_GUT²/{}", k), (asq.0.clone(), &asq.1 * nat(k))));
    }
    for &k in &[3u64, 4, 5, 9, 25, 45] { for p in 1..=2u32 {
        v.push((format!("α_GUT²/({}·d^{})", k, p),
            (asq.0.clone(), &asq.1 * nat(k * dpow(p)))));
    }}
    for &k in &[1u64, 2, 3, 4, 5] {
        v.push((format!("α_GUT³/{}", k), (acu.0.clone(), &acu.1 * nat(k))));
    }
    v
}
