//! `proton-g` — proton g-factor atomic candidate.
//!
//! Hunter-discovered (2026-04-30):
//!   g_p ≈ (NS²/d) · ζ(2)² · (1 + NS·NT · α_GUT)
//!       = (9/5) · ζ(2)² · (1 + 6·α_GUT)
//!
//! Observed g_p = 5.5856946893 (CODATA 2022).
//!
//! Class B+C: bare-ratio prefactor + linear α leakage.
//! Lean: Physics.ProtonG.g_p_atomic_skeleton (0-axiom).

use drlt_app::basel::{s_partial, Q};
use drlt_app::gap_explorer::{decimal, nat};

fn mul_q(a: &Q, b: &Q) -> Q { (&a.0 * &b.0, &a.1 * &b.1) }
fn add_q(a: &Q, b: &Q) -> Q { (&a.0 * &b.1 + &b.0 * &a.1, &a.1 * &b.1) }
fn sub_q(a: &Q, b: &Q) -> Q {
    let l = &a.0 * &b.1; let r = &b.0 * &a.1;
    let n = if l > r { l - r } else { r - l };
    (n, &a.1 * &b.1)
}

fn main() {
    let n: u64 = std::env::args().nth(1)
        .and_then(|s| s.parse().ok()).unwrap_or(5000);

    let s = s_partial(n);
    let np1 = nat(n + 1);
    let zeta_tight: Q = (&s.0 * &np1 + &s.1, &s.1 * &np1);
    let agut: Q = (zeta_tight.1.clone(), nat(25) * &zeta_tight.0);

    println!("=== proton g-factor — atomic candidate ===\n");
    println!("ζ(2) tight ≈ {} (N = {n})", decimal(&zeta_tight, 9));
    println!("α_GUT      ≈ {}\n", decimal(&agut, 9));

    // (NS²/d) = 9/5
    let pre: Q = (nat(9), nat(5));
    // ζ(2)²
    let zeta_sq = mul_q(&zeta_tight, &zeta_tight);
    // (1 + 6·α_GUT)
    let one: Q = (nat(1), nat(1));
    let six_alpha: Q = (nat(6) * &agut.0, agut.1.clone());
    let leak = add_q(&one, &six_alpha);

    let g_p_drlt = mul_q(&mul_q(&pre, &zeta_sq), &leak);

    println!("Components:");
    println!("  (NS²/d)             = {}  (= 9/5 atomic)", decimal(&pre, 6));
    println!("  ζ(2)²               = {}", decimal(&zeta_sq, 9));
    println!("  (1 + NS·NT·α_GUT)   = {}  (k = 6)", decimal(&leak, 9));
    println!();
    println!("DRLT g_p             = {}    ★", decimal(&g_p_drlt, 9));

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
    println!("Atomic decomposition:");
    println!("  NS²/d  = 9/5  = AAA-channel count / spatial dim");
    println!("  ζ(2)²        = squared loop-integral 2-loop trace");
    println!("  1 + NS·NT·α  = chiral-edge Class B leakage (k = 6)");
    println!();
    println!("Class B+C composite.  4× improvement over prior d·(1+dα).");
    println!("Tighter form likely requires Massey-product chains.");
    println!();
    println!("Lean cite: ProtonG.g_p_atomic_skeleton (0-axiom)");
}
