//! `m-tau-mu` — m_τ/m_μ from K_{3,2}^{(2)} (Lean TauOverMu.lean).
//!
//!   m_τ/m_μ = c^NS · NT · [1 + x + x² + (NS/(d+1))·x³]
//!   where x = NT · α_GUT
//!
//! base = c^NS · NT = 2³·2 = 16  (atomic integer!)
//! NS/(d+1) = 3/6 = 1/2  (cofactor)
//!
//! CODATA: m_τ = 1776.86 MeV, m_μ = 105.6584 MeV
//!         → m_τ/m_μ = 16.81687...

use drlt_app::basel::{s_partial, Q};
use drlt_app::gap_explorer::{decimal, nat};

fn add_q(a: &Q, b: &Q) -> Q { (&a.0 * &b.1 + &b.0 * &a.1, &a.1 * &b.1) }
fn mul_q(a: &Q, b: &Q) -> Q { (&a.0 * &b.0, &a.1 * &b.1) }

fn main() {
    let n: u64 = std::env::args().nth(1)
        .and_then(|s| s.parse().ok()).unwrap_or(5000);

    let s = s_partial(n);
    let np1 = nat(n + 1);
    let zeta_tight: Q = (&s.0 * &np1 + &s.1, &s.1 * &np1);
    let agut: Q = (zeta_tight.1.clone(), nat(25) * &zeta_tight.0);

    println!("=== m_τ/m_μ from K_{{3,2}}^{{(2)}} (N = {n}) ===\n");
    println!("α_GUT       ≈ {}", decimal(&agut, 12));

    // x = NT · α_GUT = 2 · α_GUT
    let x: Q = (&agut.0 * nat(2), agut.1.clone());
    println!("x = NT·α_GUT ≈ {}", decimal(&x, 12));

    let one = (nat(1), nat(1));
    let x2 = mul_q(&x, &x);
    let x3 = mul_q(&x2, &x);
    // (NS/(d+1)) · x³ = (3/6) · x³ = x³/2
    let half_x3: Q = (x3.0.clone(), &x3.1 * nat(2));

    let bracket = add_q(&add_q(&add_q(&one, &x), &x2), &half_x3);
    println!();
    println!("1               = 1.000000");
    println!("x               = {}", decimal(&x, 9));
    println!("x²              = {}", decimal(&x2, 12));
    println!("(NS/(d+1))·x³   = {}", decimal(&half_x3, 12));
    println!("[1+x+x²+x³/2]   = {}", decimal(&bracket, 9));

    // base = c^NS · NT = 16
    let base: Q = (nat(16), nat(1));
    let result = mul_q(&base, &bracket);
    // 1776.86 / 105.6584  →  17768600 / 1056584
    let observed: Q = (nat(17_768_600), nat(1_056_584));

    println!();
    println!("base (c^NS·NT) = 16");
    println!("DRLT m_τ/m_μ    = {} ★", decimal(&result, 9));
    println!("Observed       = {}  (= 1776.86/105.6584)",
        decimal(&observed, 9));

    let l = &observed.0 * &result.1;
    let r = &result.0 * &observed.1;
    let diff_num = if l > r { l - r } else { r - l };
    let diff: Q = (diff_num, &observed.1 * &result.1);
    let ppm: Q = (&diff.0 * nat(1_000_000) * &observed.1,
                  &diff.1 * &observed.0);
    println!("|Δ|             ≈ {}", decimal(&diff, 9));
    println!("                ≈ {} ppm", decimal(&ppm, 2));
    println!("\nLean cite: TauOverMu.base_eq_16 + base_decomp (0-axiom)");
}
