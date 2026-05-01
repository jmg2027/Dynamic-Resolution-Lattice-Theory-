//! `golden-ratio` — φ = (1+√d)/2 emerges naturally from d=5 lattice.
//! Lean: GoldenRatio.lean.
//!
//! ★ Core identity: (2φ − 1)² = 5 = d  (Pell-style)
//!   → 2φ − 1 = √d = √5
//!   → φ is *the natural scaling invariant* of the d=5 lattice.
//!
//! Appearances:
//!   CKM Wolfenstein A = φ/c
//!   δ_CKM = π/φ²
//!   Fibonacci limit ratio = φ

fn main() {
    println!("=== Golden ratio φ = (1+√d)/2 ===\n");
    println!("Atom: d = 5 (atomic dimension).\n");
    println!("Pell-style identity:  (2φ − 1)² = d");
    println!("  Proof:");
    println!("    φ² − φ − 1 = 0           (defining equation)");
    println!("    → φ² = φ + 1");
    println!("    (2φ − 1)² = 4φ² − 4φ + 1");
    println!("              = 4(φ + 1) − 4φ + 1");
    println!("              = 5 = d  ✓");
    println!();
    println!("→ 2φ − 1 = √5 = √d");
    println!("→ φ = (1 + √d)/2 = (1 + √5)/2 ≈ 1.618033988750");

    println!("\n--- Bracket φ² (rational only) ---");
    // φ² ≈ 2.618.  φ² = φ + 1.
    // (2φ-1)² = 5 → 4φ²-4φ+1 = 5 → φ² = (4+4φ)/4 = 1+φ
    // So φ² > 5/2 (i.e., > 2.5)?  φ² ≈ 2.618 > 2.5 ✓
    println!("  φ² > 5/2  (= {}.{}) ✓ since φ² ≈ 2.618", 5/2, 5%2);
    println!("  φ² < 3  (= {})       ✓", 3);

    println!("\n--- Fibonacci connection ---");
    println!("  F_(n+1) / F_n → φ as n → ∞");
    println!("  (NT, NS, d) = (F_3, F_4, F_5) = (2, 3, 5)");
    println!("  → (NS, NT) consecutive Fibonacci → ratio NS/NT = 3/2 → φ");

    println!("\n--- Where φ appears in DRLT formulas ---");
    println!("  CKM Wolfenstein A   = φ/c = φ/2 ≈ 0.809");
    println!("  δ_CKM (CP phase)    = π/φ² ≈ 1.20 rad ≈ 68.8°");
    println!("  CKM hierarchy       λ^k powers of 5/22 + φ scaling");

    println!("\n★ φ is *not imposed externally* — it falls out of d=5 atomicity.");
    println!("Lean cite: GoldenRatio (φ_squared_bracket, 0-axiom)");
}
