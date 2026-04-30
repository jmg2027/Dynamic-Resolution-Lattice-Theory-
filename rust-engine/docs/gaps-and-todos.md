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

## 4.  Hardcoded transcendental inputs  ✅ DOCUMENTED 2026-04-30

Two binaries that consume π as a display-only rational input now
carry explicit "⚠ External-input bracket" headers calling out:

- dark_energy.rs       : 1/π consumed display-only; certified Lean
  uses an interval bracket consistent with the finite-lattice
  principle.  Wallis-style ℕ-pair derivation = principled fix.
- deuteron_binding.rs  : 1/π plus Λ_QCD as an empirical scale —
  inheriting the §5 Λ_QCD gap until that closes.

## 5.  Λ_QCD origin still informal (HAD chain)

`m_proton`, `nuclear_binding`, and the hadron-mass ladder all assume
Λ_QCD as a unit scale.  The finite-N self-resonance section
(N(α_3)=20) hints at the answer but `Physics/HadronMassChain.lean`
does not yet close `Λ_QCD = f(NS, NT, d, c, α_GUT)` as a 0-axiom
identity.  Flag for next session.

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

- `m_t/m_c ≈ 137` cross-context coincidence with 1/α_em — *still
  open and honestly so*.  The current Lean theorem
  `Phase3.Translation.MassHierarchy.top_charm : (137 : Nat) = 137`
  is a **tautology placeholder**, not a derivation.  The substantive
  obstruction: m_b/m_c ≈ 3.29 observed vs NS = 3 atomic — DRLT does
  not yet have a closed-form correction that bridges the 10% gap.
  Per CLAUDE.md "introducing parameters to fit is not a 0-parameter
  theory", we prefer to flag this as observational until the m_b/m_c
  step has its own atomic derivation.  Forcing the integer 137 onto
  m_t/m_c without that step would catalogue, not validate.
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
