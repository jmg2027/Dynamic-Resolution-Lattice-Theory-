//! `gap-explorer` — rank 213-pure ℚ values by proximity to a target.
//!
//! Default target: α_em structural gap = 137.0359991 - 137.0354548
//!                                     = 0.0005443 = (5443, 10_000_000).
//!
//! Shows the closest DRLT-pure rationals — *no* fitting, only
//! enumeration of quantities that originate in 213 axioms.

use drlt_app::basel::Q;
use drlt_app::gap_explorer::{abs_diff, candidates, decimal, lt_q, nat};
use std::cmp::Ordering;

fn main() {
    let n: u64 = std::env::args().nth(1)
        .and_then(|s| s.parse().ok()).unwrap_or(200);
    let top: usize = std::env::args().nth(2)
        .and_then(|s| s.parse().ok()).unwrap_or(20);

    let gap: Q = (nat(5443), nat(10_000_000));
    println!("=== Gap Explorer (213 pure-ℚ inventory) ===");
    println!("Target gap = 137.0359991 − 137.0354548");
    println!("           = {} = {}/{}", decimal(&gap, 9), gap.0, gap.1);
    println!("α_GUT bracket evaluated at N = {n}");
    println!();

    let mut cands = candidates(n);
    cands.sort_by(|a, b| {
        let (da, db) = (abs_diff(&a.1, &gap), abs_diff(&b.1, &gap));
        if lt_q(&da, &db) { Ordering::Less }
        else if lt_q(&db, &da) { Ordering::Greater }
        else { Ordering::Equal }
    });

    println!("{:<28}  {:<14}  {:>12}  {:>10}",
        "label", "value", "ratio x/gap", "Δ ppm·10⁻³");
    println!("{}", "─".repeat(72));

    for (lbl, q) in cands.iter().take(top) {
        let val = decimal(q, 11);
        // ratio = q / gap (cross-mul) for display
        let r = (&q.0 * &gap.1, &q.1 * &gap.0);
        let r_str = decimal(&r, 4);
        // |Δ|/gap × 10⁶ (ppm).
        let diff = abs_diff(q, &gap);
        let dratio: Q = (&diff.0 * nat(1_000_000) * &gap.1,
                         &diff.1 * &gap.0);
        let dratio_str = decimal(&dratio, 0);
        println!("{:<28}  {:<14}  {:>12}  {:>10}",
            lbl, val, r_str, dratio_str);
    }

    println!();
    println!("note: ratio 1.0000 = exact match.  Δ ppm·10⁻³ = |x-gap|/gap × 10⁶.");
}
