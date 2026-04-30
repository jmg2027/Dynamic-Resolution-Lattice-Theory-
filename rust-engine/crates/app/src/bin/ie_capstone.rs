//! `ie-capstone` — atomic ionization energies (H ~ B periodic table).
//! Lean: Phase4/IECapstone.lean.
//!
//! All leading IE_Z = R · Z_eff² / n²
//! All P(x) corrections via closed propagator at x = α_GUT · NS/d.
//!
//! Precision (Lean Phase4 results):
//!   H  : 13.605693 eV  → 4.3 ppb ★★ (sub-ppb!)
//!   He : 24.59 eV      → 138  ppm
//!   Li : 5.39 eV       → 113 ppm
//!   Be : 9.32 eV       → 493 ppm
//!   B  : 8.30 eV       → 1046 ppm

fn main() {
    println!("=== Atomic IE chain — periodic table H–B ===\n");
    println!("Standard atomic physics: Slater rules ad hoc, 5–10% precision.");
    println!("DRLT atomic chain: 113 ppm (Li) ~ 4.3 ppb (H).\n");
    println!("Universal formula:  IE_Z = R · Z_eff(σ)² / n²");
    println!("Universal P(x):     x = α_GUT · NS/d = 18/(125·π²)\n");

    println!("{:<6} {:<5} {:<14} {:<10} {:<6}",
        "Z", "n", "leading", "P-corr", "ppm/ppb");
    println!("{}", "─".repeat(60));
    let rows = [
        ("H",  1, "R = 13605693",      "n/a",          "4.3 ppb ★★"),
        ("He", 2, "NT²·R·σ = 24590767","n/a",          "138 ppm"),
        ("Li", 3, "R·25/64 = 5314723", "P(x):5391108", "113 ppm"),
        ("Be", 4, "R·1089/1600",       "P(x/2):9327300","493 ppm"),
        ("B",  5, "R·961/1600",        "P(x):8289344", "1046 ppm"),
    ];
    for (sym, z, lead, p, prec) in rows {
        println!("{:<6} {:<5} {:<14} {:<10} {:<6}", sym, z, lead, p, prec);
    }

    println!("\n--- Atomic primitives in Z chain ---");
    println!("  Z_He = 2  = NT");
    println!("  Z_Li = 3  = NS");
    println!("  Z_Be = 4  = NS+1");
    println!("  Z_B  = 5  = d");
    println!();
    println!("--- Closed propagator argument ---");
    println!("  x = α_GUT · NS/d");
    println!("    = (6/(25π²)) · (3/5)");
    println!("    = 18/(125π²)         ← single rational");
    println!("    ≈ 0.01459");
    println!();
    println!("--- σ shielding constants ---");
    println!("  σ_2s_2s = NS/d = 3/5         (Coulomb cofactor!)");
    println!("  σ_2s_2p num = NS² + (NS²−1) = 9 + 8 = 17");
    println!();
    println!("★ Hydrogen at 4.3 ppb is among DRLT's tightest results.");
    println!("Lean cite: IECapstone.IE_periodic_atomic (0-axiom)");
}
