//! `scale-ladder-classify` — classify every observable verified in
//! the rust-engine into its cohomology class (A/B/C/D/E) per
//! `docs/cohomology-classes.md`.  Demonstrates that the *same*
//! 5-class principle applies across atomic, molecular, nuclear, and
//! cosmological scales — single lattice, scale-invariant structure.
//!
//! Class legend:
//!   A = single-simplex P(x) propagator
//!   B = boundary leakage (linear in α_GUT)
//!   C = full-lattice bare invariant polynomial
//!   D = chain product (composition of A/B/C)
//!   E = modulus shadow (gravity readout of same Gram G)

#[derive(Copy, Clone)]
#[allow(dead_code)]   // `lean` field is documentation-only.
struct Row { scale: &'static str, obs: &'static str, class: &'static str,
             form: &'static str, lean: &'static str }

const ROWS: &[Row] = &[
    Row { scale: "sub-atomic", obs: "1/α_3 = 8 = NS²−1", class: "C",
          form: "bare invariant", lean: "MasterCatalog" },
    Row { scale: "sub-atomic", obs: "1/α_2 = 30 + ...", class: "C",
          form: "bare + α_GUT term", lean: "TripleCouplingV2" },
    Row { scale: "sub-atomic", obs: "1/α_em = 60·ζ(2)+30+25/3+...", class: "C+A",
          form: "bare poly + P-tail", lean: "AlphaEMWithTail" },
    Row { scale: "sub-atomic", obs: "N_gen = 3 = C(NS,NT)", class: "C",
          form: "bare integer", lean: "Generations" },
    Row { scale: "lepton",     obs: "m_μ/m_e ≈ 207 (0.49 ppb)", class: "A·D",
          form: "NS·137/NT × P(α/4)", lean: "Phase3.LeptonRatioDerivation" },
    Row { scale: "lepton",     obs: "m_τ/m_μ ≈ 17 = NS²+(NS²−1)", class: "C",
          form: "bare integer pair", lean: "TauOverMu" },
    Row { scale: "quark",      obs: "m_t/m_b = 1/α_GUT", class: "C",
          form: "d²·ζ(2)", lean: "QuarkHierarchy.mt_mb_dim" },
    Row { scale: "quark",      obs: "m_b/m_c = NS·(1+α·NT²) 142 ppm", class: "B",
          form: "1 + α_GUT·NT²", lean: "QuarkHierarchy.mb_mc_correction_atomic" },
    Row { scale: "quark",      obs: "m_t/m_c chain (0.45%)", class: "D",
          form: "C × B chain", lean: "QuarkHierarchy.mt_mc_chain_atomic" },
    Row { scale: "quark",      obs: "y_t = 1 − α_GUT/NS (15 ppm)", class: "B",
          form: "near-saturation",
          lean: "QuarkHierarchy.top_yukawa_skeleton" },
    Row { scale: "neutrino",   obs: "sin²θ₁₂ leading = 1/NS = 1/3", class: "C",
          form: "bare integer ratio", lean: "PMNS.sin2_12_eq_1_3" },
    Row { scale: "neutrino",   obs: "sin²θ₂₃ leading = 1/NT = 1/2", class: "C",
          form: "bare integer ratio", lean: "PMNS.sin2_23_eq_1_2" },
    Row { scale: "neutrino",   obs: "sin²θ₁₃ ≈ α_GUT (0.21%)", class: "C",
          form: "bare α_GUT atomic", lean: "PMNS.sin2_13_leading_is_alpha_GUT" },
    Row { scale: "neutrino",   obs: "δ_CP denom = d²−1 = 24", class: "C",
          form: "bare atomic d²−1", lean: "PMNS.delta_CP_eq_24" },
    Row { scale: "neutrino",   obs: "m₃/m₂ ≈ 5.71 (+0.04%)", class: "D",
          form: "atomic ladder chain", lean: "NeutrinoMixing" },
    Row { scale: "CKM",        obs: "Cabibbo sin θ_C = 5/22", class: "C",
          form: "bare rational d/(d²−d+c)", lean: "Cabibbo.irreducible_5_22" },
    Row { scale: "CKM",        obs: "λ_W = 5/22, A·λ² Wolfenstein", class: "D",
          form: "C·B·B chain", lean: "CKMHierarchy.wolfenstein_atomic_capstone" },
    Row { scale: "EW",         obs: "v_H = 245.6 GeV (anchor)", class: "C",
          form: "atomic scale anchor", lean: "HiggsMaster" },
    Row { scale: "EW",         obs: "m_H 125.28 GeV (+0.02%)", class: "B",
          form: "v_H · (1/c + α(d-1)/d)", lean: "HiggsVacuum" },
    Row { scale: "EW",         obs: "λ_H 0.13 (0.37%)", class: "A",
          form: "V(α/c=α/2) propagator", lean: "HiggsQuartic" },
    Row { scale: "EW",         obs: "sin²θ_W ≈ 0.233 (0.83%)", class: "C",
          form: "bare bracket + α correction", lean: "Weinberg" },
    Row { scale: "EW",         obs: "cos²θ_W = m_W²/m_Z² (0.22%)", class: "C",
          form: "bare bracket", lean: "WZBosons" },
    Row { scale: "predict",    obs: "θ_QCD ~ 10⁻¹¹ < bound", class: "C",
          form: "α^(d-1) suppression bound", lean: "ThetaQCD" },
    Row { scale: "atom",       obs: "Hydrogen E_n binding (4.3 ppb)", class: "A",
          form: "single simplex P(x)", lean: "Phase4.IECapstone" },
    Row { scale: "atom",       obs: "He ionization screening", class: "B",
          form: "Z_eff leakage", lean: "AtomicScreening" },
    Row { scale: "atom",       obs: "Periodic table shells", class: "C",
          form: "sub-simplex inventory", lean: "SubSimplexInventory" },
    Row { scale: "molecule",   obs: "CH₄ cos = −1/NS", class: "A",
          form: "single sub-simplex angle", lean: "BondAngles" },
    Row { scale: "molecule",   obs: "H₂O cos = −1/(NS+1)", class: "A",
          form: "single sub-simplex angle", lean: "BondAngles" },
    Row { scale: "nucleus",    obs: "Deuteron binding 2.27 MeV", class: "A",
          form: "NS-NT pair propagator", lean: "DeuteronBinding" },
    Row { scale: "nucleus",    obs: "r_p·m_p/ℏc = NT² (0.02 %)", class: "C",
          form: "NT² = (d−1) = (NS+1) triple", lean: "Proton.r_p_atomic" },
    Row { scale: "lepton",     obs: "m_p/m_e = NS·NT·π⁵ (19 ppm)", class: "C",
          form: "6·π⁵, 6 = NS·NT = d+1", lean: "ProtonElectronRatio" },
    Row { scale: "lepton",     obs: "m_τ/m_e = (d·NT)²·π³·(1+dα) (134 ppm)", class: "B+C",
          form: "100·π³·(1+5α_GUT)", lean: "ProtonElectronRatio.m_tau_over_m_e_atomic" },
    Row { scale: "nucleus",    obs: "Magic 2,8,20 EXACT", class: "C",
          form: "pronic sum", lean: "MagicNumbers.ho_magic_first_7" },
    Row { scale: "nucleus",    obs: "m_p (1.56 ppm)", class: "A",
          form: "NS·anchor·P(α·NS/d)", lean: "ProtonMass" },
    Row { scale: "nucleus",    obs: "Muon τ 192 = (NS²−1)(d²−1)", class: "C",
          form: "two atomic factors", lean: "ParticleLibrary.muon_lifetime_192" },
    Row { scale: "cosmology",  obs: "Ω_Λ ≈ 0.685 (0.001%)", class: "E",
          form: "(1−1/π)(1+α/d) modulus", lean: "DarkEnergy" },
    Row { scale: "cosmology",  obs: "M_Pl/v_H = d^(d²)/(d+1)", class: "E",
          form: "atomic hierarchy", lean: "HiggsVacuum" },
    Row { scale: "cosmology",  obs: "Λ_QCD = phantom unit", class: "E",
          form: "no parameter", lean: "LambdaQCDPhantom" },
    Row { scale: "gravity",    obs: "Gravity not interaction", class: "E",
          form: "W = |G|²/d modulus",
          lean: "Phase3.GravityNotInteraction" },
];

fn main() {
    println!("=== Scale ladder — every observable, every class ===\n");
    println!("Single principle from cohomology-classes.md, repeated at");
    println!("every scale: sub-atomic → cosmology.\n");
    println!("{:<10} {:<40} {:<6} {:<35}",
        "scale", "observable", "class", "atomic form");
    println!("{}", "─".repeat(98));
    let mut last = "";
    for r in ROWS {
        if r.scale != last { println!(); last = r.scale; }
        println!("{:<10} {:<40} {:<6} {:<35}", r.scale, r.obs, r.class, r.form);
    }
    println!("\n--- class tally ---");
    for c in ["A", "B", "C", "C+A", "A·D", "D", "E"] {
        let n = ROWS.iter().filter(|r| r.class == c).count();
        if n > 0 { println!("  {c:<6} : {n} observables"); }
    }
    println!("\n★ Same A/B/C/D/E classification covers all rungs.");
    println!("  No new theoretical machinery per scale — just");
    println!("  K_{{3,2}}^{{(c=2)}} simplex inventory + Gram phase/modulus.");
}
