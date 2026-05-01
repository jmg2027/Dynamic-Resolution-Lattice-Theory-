//! `proton-g` — proton g-factor pure-rational Class D triple cup form.
//!
//! Found 2026-05-01 via atomic-hunter on rational-only bases:
//!
//!   g_p = (d²−NS)/NT² · (1 + NS·NT·α_GUT) · (1 − NS·d·α_em)
//!                     · (1 − NS²·NT·d·α_em²)
//!       = (22/4) · (1 + 6·α_GUT) · (1 − 15·α_em) · (1 − 90·α_em²)
//!
//!   matches CODATA 5.5856946893 at 0.097 ppm (8500× tighter than
//!   the prior (9/5)·ζ²·(1+6α_GUT) Class B+C form at 828 ppm).
//!
//! Reading: Cabibbo-numerator base · α_GUT leak · α_em leak ·
//! α_em² double-cup.  90 = NT·45 (NT × m_n/m_p coefficient) —
//! the same K_25 cup-chain anchor reused.
//!
//! Lean: Physics.ProtonG.g_p_v2_atomic (0-axiom).

use drlt_app::basel::Q;
use drlt_app::gap_explorer::{decimal, nat};

fn mul_q(a: &Q, b: &Q) -> Q { (&a.0 * &b.0, &a.1 * &b.1) }
fn add_q(a: &Q, b: &Q) -> Q { (&a.0 * &b.1 + &b.0 * &a.1, &a.1 * &b.1) }
fn sub_q(a: &Q, b: &Q) -> Q {
    let l = &a.0 * &b.1; let r = &b.0 * &a.1;
    let n = if l > r { l - r } else { r - l };
    (n, &a.1 * &b.1)
}

fn alpha_em_q() -> Q { (nat(10_000_000u64), nat(1370359991u64)) }

fn main() {
    let n: u64 = std::env::args().nth(1)
        .and_then(|s| s.parse().ok()).unwrap_or(5000);

    // α_GUT = 1/(d²·ζ(2)) computed from Basel partial sum
    let s = drlt_app::basel::s_partial(n);
    let np1 = nat(n + 1);
    let zeta_tight: Q = (&s.0 * &np1 + &s.1, &s.1 * &np1);
    let agut: Q = (zeta_tight.1.clone(), nat(25) * &zeta_tight.0);
    let aem = alpha_em_q();

    println!("=== proton g-factor — pure rational Class D triple cup ===\n");
    println!("α_GUT ≈ {} (Basel N={n})", decimal(&agut, 9));
    println!("α_em  ≈ {}", decimal(&aem, 12));
    println!();

    // base = (d²−NS)/NT² = 22/4
    let base: Q = (nat(22u64), nat(4u64));
    let one: Q = (nat(1u64), nat(1u64));

    // (1 + 6·α_GUT)
    let f1 = add_q(&one, &(nat(6u64) * &agut.0, agut.1.clone()));
    // (1 − 15·α_em)
    let f2 = sub_q(&one, &(nat(15u64) * &aem.0, aem.1.clone()));
    // (1 − 90·α_em²)
    let aem2 = mul_q(&aem, &aem);
    let f3 = sub_q(&one, &(nat(90u64) * &aem2.0, aem2.1.clone()));

    let g_p_drlt = mul_q(&mul_q(&mul_q(&base, &f1), &f2), &f3);

    println!("Components:");
    println!("  (d²−NS)/NT²       = 22/4 = {}", decimal(&base, 6));
    println!("  (1 + NS·NT·α_GUT) = {}  (k=6)", decimal(&f1, 9));
    println!("  (1 − NS·d·α_em)   = {}  (k=15)", decimal(&f2, 12));
    println!("  (1 − NS²·NT·d·α_em²) = {}  (k=90)", decimal(&f3, 12));
    println!();
    println!("DRLT g_p             = {}    ★", decimal(&g_p_drlt, 12));

    // CODATA: 5.5856946893
    let observed: Q = (nat(55856946893u64), nat(10_000_000_000u64));
    println!("Observed g_p (CODATA)= {}", decimal(&observed, 9));

    let dq = sub_q(&observed, &g_p_drlt);
    let ppm = mul_q(&mul_q(&dq, &(nat(1_000_000), nat(1))),
                    &(observed.1.clone(), observed.0.clone()));
    println!();
    println!("|Δ|                  = {}", decimal(&dq, 6));
    println!("                     ≈ {} ppm  ★", decimal(&ppm, 1));

    println!();
    println!("Atomic decomposition (all (NS,NT,d) primitive counts):");
    println!("  22 = d² − NS    (Cabibbo numerator)");
    println!("  4  = NT²        (chirality phase)");
    println!("  6  = NS·NT      (bipartite spoke count)");
    println!("  15 = NS·d       (S-channel × spatial)");
    println!("  90 = NS²·NT·d   (= NT × 45, 45 = m_n/m_p coef)");
    println!();
    println!("Class D triple cup-chain — 8500× tighter than ζ(2)² form.");
    println!("Lean cite: ProtonG.g_p_v2_atomic (0-axiom)");
}
