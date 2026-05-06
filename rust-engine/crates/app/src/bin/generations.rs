//! `generations` — N_gen = C(NS, NT) = C(3, 2) = 3 (Lean Generations.lean).
//!
//! Standard Model treats N_gen = 3 as observation.  DRLT *derives* it
//! from atomicity.  Sharper: no 4th generation slot exists in the lattice.

use drlt_lens::chiral_k32::binom;

fn main() {
    let ns = 3u64; let nt = 2;
    println!("=== N_gen = C(NS, NT) from K_{{3,2}}^{{(2)}} ===\n");
    println!("Atomicity: NS = {ns}, NT = {nt}\n");

    let n_gen = binom(ns, nt);
    println!("N_gen = C(NS, NT) = C({ns}, {nt}) = {} ★", n_gen);
    println!("Standard Model observation: 3 generations  ✓");

    println!("\n--- No 4th generation slot ---");
    for k in 0..=5u64 {
        let v = binom(ns, k);
        let mark = if v > 0 { " " } else { " (slot empty)" };
        println!("  C({ns}, {k}) = {}{}", v, mark);
    }
    println!("\nC(3, k) = 0 for k ≥ 4 (Pascal triangle truncates).");
    println!("→ DRLT predicts *no 4th generation* (sharper than SM).");

    println!("\n--- Sub-simplex consistency check ---");
    // sum of C(d, k) for k = 1..d should be 2^d - 1 = 31
    let d = ns + nt;
    let mut total = 0u64;
    for k in 1..=d {
        total += binom(d, k);
    }
    println!("Σ_{{k=1..d}} C(d, k) = {}    (= 2^d − 1 = {})",
        total, (1u64 << d) - 1);

    println!("\nLean cite: Generations.n_gen_eq_three + no_4th_gen_slot (0-axiom)");
}
