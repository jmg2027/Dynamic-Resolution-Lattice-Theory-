//! `mb-mc-sweep` — m_b/m_c correction sweep (added 2026-04-30).
//!
//! Observed PDG: m_b ≈ 4.18 GeV, m_c ≈ 1.27 GeV → ratio 3.2913.
//! NS=3 base (3rd-gen quark spatial cutoff, gaps-and-todos.md §7c).
//! Residual = 3.2913 − 3 = 0.2913 from "Beyond NS=3" leakage:
//! signal at the b_1=8 cycle-space edge crosses the chiral-split
//! boundary into the NT=2 sector via an atomic correction tensor.
//!
//! Sweep both correction forms over small atomic k ∈ ℕ:
//!   linear   :  m_b/m_c = NS · (1 + α_GUT · k)
//!   propagator: m_b/m_c = NS · P(α_GUT · k),  P(x) = (1+2x)/(1+x)
//! and rank by | DRLT − 3.2913 |.
//!
//! ⚠ Diagnostic, not certified.  Closure to a Lean theorem requires
//! a counting derivation of whichever atomic k wins (NT², d−1, ...).

use drlt_app::basel::{s_partial, Q};
use drlt_app::gap_explorer::{decimal, lt_q, nat};

fn add_q(a: &Q, b: &Q) -> Q { (&a.0 * &b.1 + &b.0 * &a.1, &a.1 * &b.1) }
fn mul_q(a: &Q, b: &Q) -> Q { (&a.0 * &b.0, &a.1 * &b.1) }
fn sub_q(a: &Q, b: &Q) -> Q {
    let l = &a.0 * &b.1; let r = &b.0 * &a.1;
    let n = if l > r { l - r } else { r - l };
    (n, &a.1 * &b.1)
}

fn atomic_ks() -> Vec<(&'static str, u64)> {
    vec![
        ("NS",            3),  ("NT",            2),  ("d",         5),
        ("NT²=4",         4),  ("NS²=9",         9),  ("(NS²−1)=8", 8),
        ("(d²−1)=24",    24),  ("NS·NT=6",       6),  ("NS·d=15",  15),
        ("NT·d=10",      10),  ("d²=25",        25),  ("F_7=13",   13),
    ]
}

fn p_of(x: &Q) -> Q { (&x.1 + nat(2) * &x.0, &x.1 + &x.0) }

fn main() {
    let n: u64 = std::env::args().nth(1).and_then(|s| s.parse().ok()).unwrap_or(5000);
    let s = s_partial(n);
    let np1 = nat(n + 1);
    let zeta_tight: Q = (&s.0 * &np1 + &s.1, &s.1 * &np1);
    let agut: Q = (zeta_tight.1.clone(), nat(25) * &zeta_tight.0);

    // observed: 4.18 / 1.27 = 418/127
    let target: Q = (nat(418), nat(127));
    let three: Q = (nat(3), nat(1));

    println!("=== m_b/m_c residual sweep — Beyond NS=3 ===\n");
    println!("Observed PDG:    m_b/m_c = 418/127 ≈ {}", decimal(&target, 6));
    println!("NS=3 base:       3.000000  (Δ = {} ≈ +9.7%)",
        decimal(&sub_q(&target, &three), 6));
    println!("α_GUT bracket  ≈ {} (N={n})\n", decimal(&agut, 9));

    println!("--- Linear:  NS · (1 + α_GUT · k) ---");
    println!("{:<14} {:<14} {:<12}", "k", "DRLT", "|Δ|");
    sweep(&agut, &target, true);

    println!("\n--- Propagator:  NS · P(α_GUT · k) ---");
    println!("{:<14} {:<14} {:<12}", "k", "DRLT", "|Δ|");
    sweep(&agut, &target, false);

    println!("\n→ leading hypothesis: NS · (1 + α_GUT · NT²) = NS · (1 + 4α_GUT)");
    println!("   atomic interpretation: NT² = 4 = (d−1) = (NS+1) — three");
    println!("   independent atomic readings of the same integer at d=5.");
    println!("   Lean candidate: `mb_mc_atomic` in QuarkHierarchy (TBD).");
}

fn sweep(agut: &Q, target: &Q, linear: bool) {
    let mut rows: Vec<(String, Q, Q, bool)> = Vec::new();
    let three: Q = (nat(3), nat(1));
    let one: Q = (nat(1), nat(1));
    for (label, kv) in atomic_ks() {
        let x: Q = (&agut.0 * nat(kv), agut.1.clone());
        let factor = if linear { add_q(&one, &x) } else { p_of(&x) };
        let drlt = mul_q(&three, &factor);
        let neg = lt_q(&drlt, target);
        let dq = sub_q(&drlt, target);
        rows.push((label.to_string(), drlt, dq, neg));
    }
    // sort by absolute deviation (cross-mul on Δ)
    rows.sort_by(|a, b| {
        let la = &a.2.0 * &b.2.1; let lb = &b.2.0 * &a.2.1;
        la.cmp(&lb)
    });
    for (label, drlt, dq, neg) in rows.iter().take(8) {
        let sign = if *neg { "−" } else { "+" };
        println!("  {label:<14} {:<14} {sign}{}",
            decimal(drlt, 6), decimal(dq, 6));
    }
}