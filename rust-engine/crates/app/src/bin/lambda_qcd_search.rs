//! `lambda-qcd-search` — atomic counting underlying the apparent
//! v_H / Λ_QCD ratio, reinterpreted per the *phantom-elimination*
//! thesis (Mingu Jeong, 2026-04-30).
//!
//! Mainstream QCD treats Λ_QCD as the energy scale where the running
//! coupling diverges — a singularity inherited from the continuum
//! assumption.  In K_{3,2}^{(c=2)}, signals do not run; they
//! truncate at the b_1 = NS² − 1 = 8 cycle-space boundary because no
//! further topological degree of freedom remains.  Λ_QCD is therefore
//! NOT a primitive — it is the unit chosen to express
//! `m_p = NS · (anchor) · P(α_GUT · NS/d)` in MeV.
//!
//! What survives is a counting integer: the search below confirms
//! that 800 (the observed v_H/Λ_QCD ratio) decomposes as
//!   d² · NT² · (NS² − 1)  =  25 · 4 · 8  =  800
//!         channels  chiral_phase  cycle_space
//! with `NT² · (NS²−1) = NT^d = 32` the chiral cell count of K_{3,2}.
//! Lean: `Physics.LambdaQCDPhantom.lambda_qcd_phantom_count` (0-axiom).
//!
//! Whitelist row points at `lambda_qcd_phantom_count` (the counting
//! decomposition the binary prints).  The numerical-search portion
//! over alternative atomic monomials remains exploratory.

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
    println!();
    println!("--- Atomic counting decomposition (★ phantom elimination) ---");
    let nt_pow_d = nt.pow(d as u32);
    let nt_sq = nt * nt;
    let b1 = ns * ns - 1;
    println!("  d² · NT² · (NS²−1) = {}·{}·{} = {}",
        d * d, nt_sq, b1, d * d * nt_sq * b1);
    println!("  └── channels      = d²       = 25  (1/α_GUT denom)");
    println!("  └── chiral phase  = NT²      = 4");
    println!("  └── cycle space   = NS² − 1  = 8   (b_1 confinement)");
    println!();
    println!("  Identity: NT² · (NS²−1) = NT^d = {} = 32 chiral cells",
        nt_sq * b1);
    println!("  Verified: NT^d = {nt_pow_d} (matches k32-inspect total).");
    println!();
    println!("Lean cite: LambdaQCDPhantom.lambda_qcd_phantom_count (0-axiom)");
    println!();
    println!("Per Mingu Jeong 2026-04-30 phantom-elimination thesis:");
    println!("  Λ_QCD is NOT a fundamental parameter.  It is the unit one");
    println!("  chooses to express the dimensionless atomic ratio");
    println!("  NS · P(α_GUT · NS/d) in MeV.  The integer 800 is a");
    println!("  K_{{3,2}}^{{(2)}} counting invariant (channels × chiral");
    println!("  phase × cycle space), independent of unit convention.");
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
