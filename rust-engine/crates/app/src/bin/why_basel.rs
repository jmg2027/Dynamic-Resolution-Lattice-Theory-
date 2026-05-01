//! `why-basel` — why ζ(2) = Σ 1/n² shows up in DRLT physics.
//! Lean: WhyBasel.lean.
//!
//! ★ Solid-angle propagator in NS=3 spatial dim:
//!   D(n) = A_source / n^(NS−1) = 1/n²
//!
//! NS = 3 forced by atomicity → propagator exponent = 2 → 1/n²
//! → Σ 1/n² = ζ(2) = π²/6 enters every coupling.
//!
//! THIS is *why* π² appears in 1/α_em — not arbitrary, forced by NS=3.

use drlt_app::basel::s_partial;
use drlt_app::gap_explorer::decimal;

fn main() {
    let n: u64 = std::env::args().nth(1)
        .and_then(|s| s.parse().ok()).unwrap_or(20);
    let ns = 3u64;
    println!("=== Why ζ(2) ? — propagator exponent = NS − 1 ===\n");
    println!("Spatial dim NS = {} (forced by Atomicity + canonical_partition)", ns);
    println!("Solid-angle propagator: D(n) = A_source / n^(NS − 1)");
    println!("                            = 1/n^{}              [NS−1]", ns - 1);
    println!("                            = 1/n²                  [NS=3]");
    println!();
    println!("So D(n) = 1/n² is the **Basel weight** — emerges from NS=3.");
    println!();
    println!("If NS were different:");
    println!("  NS=2 → D(n) = 1/n  (logarithmic divergence)");
    println!("  NS=3 → D(n) = 1/n² (Basel = ζ(2) = π²/6) ★");
    println!("  NS=4 → D(n) = 1/n³ (ζ(3) Apéry's)");
    println!("  NS=5 → D(n) = 1/n⁴ (ζ(4) = π⁴/90)");
    println!();
    println!("✓ NS=3 is *uniquely* the dimension where Basel sum applies.");
    println!();

    println!("--- Concrete propagator weights at small n ---");
    println!("  D(1) = 1/1² = 1");
    println!("  D(2) = 1/2² = 1/4");
    println!("  D(3) = 1/3² = 1/9");
    println!("  D(4) = 1/4² = 1/16");
    println!("  ...");
    println!("  S(N) = Σ D(n) = Σ 1/n² → ζ(2) = π²/6");
    println!();

    let s = s_partial(n);
    println!("--- Numerical bracket S({n}) = ---");
    println!("  S({n}) = {} = {}/{}", decimal(&s, 9), s.0, s.1);
    println!("  ζ(2) ≈ 1.644934 (limit)");
    println!();

    // Convert ζ(2) = π²/6 to π² = 6·ζ(2) → 1/α_GUT etc.
    println!("--- π² / 6 = ζ(2) ---");
    println!("  → π² = 6·ζ(2) = 9.870");
    println!("  → 10·π² = 60·ζ(2) ← appears in 1/α_em!");
    println!("  → α_GUT = 6/(25·π²) = 1/(25·ζ(2)) — same atomic origin");

    println!("\n★ Every appearance of π or ζ(2) in DRLT formulas traces to");
    println!("  NS = 3 spatial dim → propagator exponent = 2 → Basel.");
    println!("\nLean cite: WhyBasel.prop_exponent_eq_2 (= NS − 1, 0-axiom)");
}
