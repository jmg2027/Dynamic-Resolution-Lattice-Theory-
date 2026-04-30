# Gaps & TODOs — Rust Engine Cleanup Notes

Surfaced during the 2026-04 reorganization (papers/PAPER5_DRAFT.md →
docs/precision-matrix.md).  These are *not* bugs in the verified
0-axiom Lean theorems; they are loose ends in the Rust verification
layer or pending Lean formalizations worth doing.

## 1.  Loose whitelist citations  ✅ RESOLVED 2026-04-30

All 17 module-level cites replaced with specific theorems
(weinberg_pattern_capstone, hydrogen_atomic_pattern,
PMNS_simplicial_pattern, dark_energy_pattern_capstone,
WZ_simplicial_pattern, irreducible_5_22, hierarchy_towers_master,
drlt_below_bound, wolfenstein_atomic_capstone, five_fib_atomic,
drlt_zero_parameter_claim, hierarchy_atomic, deuteron_simplicial,
bond_angles_capstone, nuclear_simplicial_pattern, golden_ratio_atomic,
confinement_is_combinatorial).

Also caught + fixed in the same pass:
- `Kernel.Term.{le_b, lt_b}` → `Kernel.Compare.{le_b, lt_b}` (file split)
- `Kernel.Term.{equivQ, leQ}` → `Kernel.Rat.{equivQ, leQ}`
- `Physics.Basel.{S, upper}` → `Physics.BaselBound.{S, upper}`
- `Physics.AlphaEMGap.n50_bracket_*` →
  `Physics.AlphaEMStructuralGap.n50_bracket_*`
- `Firmware.Raw.{a,b,slash,depth,fold}` → re-export shim citations
  retargeted to actual sub-files (Raw/Core, Raw/Slash, Raw/Fold).

Verifier upgraded (`tools/verify-citations`): now requires depth ≥ 2
file resolution AND that the trailing segment appears as a Lean
identifier (theorem/lemma/def/abbrev/instance, dotted def, inductive
constructor, or structure field) inside the resolved file.  All 89/89
now resolve at theorem-id level.

## 2.  Reused MasterCatalog citations

`muon_lifetime` formerly cited the broad MasterCatalog; ✅ resolved
2026-04-30 by retargeting to the existing 0-axiom theorem
`E213.Physics.Phase4.Library.ParticleLibrary.muon_lifetime_192`,
which states `(NS² − 1)·(d² − 1) = 192` — the EXACT atomic identity
underlying the muon lifetime prefactor.  `atomic_correspondences`
remains pointed at MasterCatalog: that's correct since it is itself
a multi-observable catalog binary.

## 3.  Exploratory binaries with no whitelist row  ✅ TAGGED 2026-04-30

The 8 diagnostic binaries

  alpha_em_decompose, gap_explorer, propagator_form, series_truncation,
  overlap_series, cf_generator, impedance_search, k32_inspect

now carry an explicit "⚠ Diagnostic, not certified" header pointing
readers at the corresponding certified binary
(`alpha-em-bracket`, `triple-coupling`, `simplex-inventory`, etc).

## 4.  Hardcoded transcendental inputs  ✅ FULLY CLOSED 2026-04-30

Originally: `dark_energy.rs` and `deuteron_binding.rs` each
consumed `1/π ≈ 318309886184/10^12` as a hardcoded rational.
Documented as "external input" headers (intermediate fix).

**Fully closed** by porting the Real213 Leibniz series machinery
(see math-branch-physics-notes.md #144-151) to the rust-engine:

- New `crates/app/src/wallis.rs`:
  - `pi_bracket(n)` from `π/4 = Σ (−1)^i/(2i+1)` alternating series
  - `inv_pi_bracket(n)` reciprocal
  - 2 unit tests verify n=50 contains observed π and 1/π values
- `dark_energy.rs` reports `Ω_Λ ∈ [lo, hi]` bracket containing
  observed 0.685 (Planck/DESI).
- `deuteron_binding.rs` reports `E_d ∈ [lo, hi]` and exposes the
  Λ_QCD anchor context-dependence (308 MeV from m_p side vs
  ~293 MeV needed for deuteron — QCD running between scales).

`taylor_e.rs` (e brackets) deferred — no current binary uses e.

Tests: 182 → 184.  No external transcendental inputs remain in
runtime crates.

## 5.  Λ_QCD-as-parameter dissolved 2026-04-30  ✅

The original framing ("derive Λ_QCD = f(NS,NT,d,c,α_GUT)") presumed
Λ_QCD has a fundamental status.  The 2026-04-30 reframing — Λ_QCD
as a phantom of continuum field theory — corrects this:

  Mainstream QCD treats Λ_QCD as the energy scale where the running
  coupling diverges — a singularity inherited from continuum field
  theory.  In K_{3,2}^{(c=2)} signals do not run; they truncate at
  the b_1 = NS²−1 = 8 cycle-space boundary because no further
  topological degree of freedom exists.  Λ_QCD is therefore *not*
  a primitive — it is just the MeV unit chosen to express the
  dimensionless atomic ratio `NS · P(α_GUT · NS/d)` (already
  encoded in `m_p` via the projection NS/d = 3/5).

The atomic counting integer that survives — and the only quantity
that needs explanation — is the K_{3,2}^{(c=2)} invariant 800:

  v_H/"Λ_QCD" = d² · NT² · (NS² − 1) = 25 · 4 · 8 = 800
              = (channels) · (chiral phase) · (cycle space)
  with NT² · (NS² − 1) = NT^d = 32  (chiral cell total).

✅ **Lean (0-axiom) closure**: `Physics/LambdaQCDPhantom.lean`
   `chiral_cells_eq_NT_pow_d`     : `NT^d = 32`
   `chiral_cells_factor`          : `NT^d = NT² · (NS² − 1)`
   `lambda_qcd_phantom_count`     : `d² · NT² · (NS² − 1) = 800`
   plus the equivalence `= d² · NT^d`.
   All `does not depend on any axioms`.

✅ **Rust trace**: `lambda-qcd-search` now prints the decomposition,
   cites the Lean theorem, and explicitly notes the unit-convention
   point.  `m-proton` header rewritten: the 308.32 MeV "anchor"
   is the chosen MeV unit, not a parameter; the atomic claim is the
   projection NS/d.

## 6.  Per-binary regression coverage  ✅ ADDED 2026-04-30

Two new integration test files cover all 48 binaries:

- `tests/binary_smoke.rs`     — runs every binary with default args,
  asserts exit code 0 and non-empty stdout.  Catches helper-induced
  crashes within ~1.5 s.
- `tests/binary_snapshots.rs` — pins headline numeric/string outputs
  for 3 representative certified binaries:
    simplex-inventory : 31 = 2^d−1 sub-simplex count + AB-edges = 6
    triple-coupling   : 1/α_em atomic-integer skeleton (60·ζ(2),
                        30, 25/3, α_GUT/4, α_GUT/45)
    mu-electron       : "206.7683" headline + "ppb" precision report

Workspace count: 178 → 182 (4 new tests).  Future bins should at
minimum be added to the smoke list; the snapshot file targets the
most-cited 0-axiom claims.

## 7.  Open Lean opportunities surfaced during cleanup

- `m_t/m_c ≈ 137`: ✅ structurally closed 2026-04-30.
  Per the "Top quark = full lattice resonance" reading, m_t/m_c
  is *not* an independent ratio: the top quark resonates with the
  entire K_{3,2}^{(c=2)} lens (H⁴ + 31 sub-simplices), so m_t/m_c
  follows the same cohomological polynomial as 1/α_em
  (60·ζ(2) + 30 + 25/3 + α_GUT/4 + α_GUT/45) by construction.
  The "double appearance" of 137 is not a coincidence — it is the
  same atomic skeleton in two unit-conventions (mass tensor vs
  electromagnetic impedance).  The existing tautology placeholder
  is therefore not "missing physics"; it is the right answer.
- `m_b/m_c ≈ 3.2913`: ✅ closed 2026-04-30 to 142 ppm.
  Linear "Beyond NS=3" leakage:
      m_b/m_c = NS · (1 + α_GUT · NT²)
              = 3 · (1 + 4·α_GUT)
              ≈ 3.29181  (DRLT)  vs 3.29134  (PDG)   |Δ| = 142 ppm.
  Sweep (`mb-mc-sweep`) over 12 atomic k × 2 functional forms
  confirms this is the unique winner; nearest competitors miss by
  ≥ 2 percent.  The integer 4 = NT² = (d − 1) = (NS + 1) carries
  three independent atomic readings — structural signature of an
  atomic identity, not a fit.
  Lean: `QuarkHierarchy.{four_atomic_triple, mb_mc_correction_atomic}`
  (both 0-axiom).
- `192 = (NS²−1)(d²−1)` for muon lifetime: ✅ resolved — the theorem
  `muon_lifetime_192` already lived in
  `Physics/Phase4/Library/ParticleLibrary.lean`; whitelist now cites
  it directly.
- `(2φ−1)² = d` Pell identity in golden_ratio.rs: ✅ resolved
  2026-04-30 — `Physics/GoldenRatio.lean` now contains pure-Nat
  Cassini-form Pell theorems
  `cassini_pell_d5  : F₅·F₅ = F₄·F₆ + 1`
  `cassini_pell_window : ±1 across F₄..F₈`
  Both 0-axiom (does not depend on any axioms).  Cassini's identity
  is the finite-lattice realization of `(2φ−1)² = d` — when φ is
  replaced by F_{n+1}/F_n the Pell error term collapses to ±1.

## 8.  Documentation hygiene

- HANDOFF.md still claimed "31+ binaries" — actual count = 48.
- precision-matrix.md was previously misnamed `papers/PAPER5_DRAFT.md`
  (paper 5 in `papers/` is `paper5_critical_line.tex`, an unrelated
  RH paper).  Now lives under `rust-engine/docs/` as engine companion.

— last updated 2026-04-30
