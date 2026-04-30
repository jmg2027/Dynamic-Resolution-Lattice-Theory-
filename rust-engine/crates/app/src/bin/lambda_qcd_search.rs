//! `lambda-qcd-search` — enumerate atomic ratios for v_H / Λ_QCD,
//! rank by proximity to observed.  The §5 Λ_QCD-origin gap calls for
//! a *counting* (not running-coupling) derivation per CLAUDE.md
//! Algebraic Priority.  This binary is the first step: search the
//! space of polynomials in {NS, NT, d, c, NS²−1, d²−1, ...} for a
//! clean integer match.
//!
//! ⚠ Diagnostic, not certified.  No row in `whitelist.toml` —
//! exploration only.  A clean match here only motivates a Lean
//! formalization; numerical agreement alone is not sufficient
//! (CLAUDE.md "Numerical agreement alone is not sufficient").

fn main() {
    // Observed:  v_H ≈ 246 GeV (EW vev),  Λ_QCD ≈ 308 MeV (MSbar).
    // Ratio v_H / Λ_QCD ≈ 246 000 / 308 = 798.7 (scheme-dependent).
    // Use the integer 798 as observed-anchor; window ≈ ±2.5%
    let target_lo = 780u64;
    let target_hi = 820u64;
    println!("=== Λ_QCD search — v_H/Λ_QCD atomic candidates ===\n");
    println!("Observed v_H ≈ 246 GeV, Λ_QCD ≈ 308 MeV (MSbar)");
    println!("→ ratio ≈ 798.7  (target window [{target_lo}, {target_hi}])\n");

    let ns: u64 = 3; let nt: u64 = 2; let d: u64 = 5;

    let primitives: &[(u64, &str)] = &[
        (ns, "NS"), (nt, "NT"), (d, "d"),
        (ns * ns - 1, "(NS²−1)"),
        (ns * ns, "NS²"),
        (ns * ns + 1, "(NS²+1)"),
        (d * d, "d²"),
        (d * d - 1, "(d²−1)"),
        (d * d * d, "d³"),
        (nt.pow(d as u32), "NT^d"),         // 32 = 2^d
        (d.pow(d as u32), "d^d"),           // 3125
        (ns * d, "NS·d"),                    // 15
        (nt * d, "NT·d"),                    // 10
        (ns + d, "NS+d"),
        (ns * ns + ns + 1, "(NS²+NS+1)"),    // 13 = F_7
    ];
    search(primitives, target_lo, target_hi);

    // Three-factor highlight from the d²·NT^d hypothesis.
    println!("\n--- d²·NT^d highlight ---");
    let dsq_ntd = d * d * nt.pow(d as u32);
    let dev = (dsq_ntd as f64 / 798.7 - 1.0) * 100.0;
    println!("  d²·NT^d = {}·{} = {}    Δ = {:+.3}%",
        d * d, nt.pow(d as u32), dsq_ntd, dev);
    println!("  → if v_H/Λ_QCD = d²·NT^d = 800, then Λ_QCD = v_H/800");
    println!("    Λ_QCD ≈ 246 GeV / 800 = 307.5 MeV  vs obs 308 MeV");

    println!("\n⚠ This is observation-driven, not a derivation.");
    println!("  Per CLAUDE.md: numerical match alone is *not* validation.");
    println!("  Next step: derive 800 from K_{{3,2}}^{{(2)}} counting,");
    println!("  e.g. via dimensional transmutation = lattice rank flow.");
}

fn search(primitives: &[(u64, &str)], lo: u64, hi: u64) {
    let mut hits: Vec<(u64, String, f64)> = Vec::new();
    for (a, na) in primitives {
        for (b, nb) in primitives {
            let prod = a.saturating_mul(*b);
            if prod >= lo && prod <= hi {
                let dev = (prod as f64 / 798.7 - 1.0) * 100.0;
                hits.push((prod, format!("{na}·{nb}"), dev));
            }
        }
    }
    hits.sort_by_key(|h| (h.0 as i64 - 798).abs());
    hits.dedup_by_key(|h| h.0);

    println!("--- 2-factor candidates in [{lo}, {hi}] ---");
    println!("{:<6} {:<28} {:<10}", "value", "atomic form", "Δ (%)");
    println!("{}", "─".repeat(50));
    for (v, form, d) in hits.iter().take(15) {
        println!("{v:<6} {form:<28} {d:>+8.3}");
    }
    if hits.is_empty() { println!("(no 2-factor hits)"); }
}
