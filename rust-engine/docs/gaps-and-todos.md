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

`muon_lifetime` and `atomic_correspondences` both cite
`E213.Physics.MasterCatalog.master_atomic_catalog`.  For
muon_lifetime, the lifetime formula τ = 192·π³/(G_F²·m_μ⁵) deserves
its own Lean theorem (the `192 = 8·24 = (NS²−1)(d²−1)` identity is
EXACT — easy 0-axiom prize).

## 3.  Exploratory binaries with no whitelist row

  alpha_em_decompose, gap_explorer, propagator_form, series_truncation,
  overlap_series, cf_generator, impedance_search, k32_inspect

These are diagnostic / number-search tools, not verification claims —
no Lean theorem to cite.  Acceptable as-is, but tag them in source
comments as "diagnostic, not certified" so future readers don't
mistake their outputs for engine certificates.

## 4.  Hardcoded transcendental inputs

CLAUDE.md notes the lattice is finite ⇒ π and ζ(2) should appear only
through bounded rational brackets.  Two binaries still print an
intermediate decimal of π/ζ(2) for human readability:

- dark_energy.rs        : Ω_Λ derivation prints π² ≈ 9.8696 informally
- deuteron_binding.rs   : nuclear scale uses π in geometric factor

Both are display-only; the underlying ℚ-pair arithmetic is
bracket-based.  Worth a one-line "external input bracket" header
comment in each.

## 5.  Λ_QCD origin still informal (HAD chain)

`m_proton`, `nuclear_binding`, and the hadron-mass ladder all assume
Λ_QCD as a unit scale.  The finite-N self-resonance section
(N(α_3)=20) hints at the answer but `Physics/HadronMassChain.lean`
does not yet close `Λ_QCD = f(NS, NT, d, c, α_GUT)` as a 0-axiom
identity.  Flag for next session.

## 6.  No per-binary unit tests

178/178 workspace tests pass, but every `crates/app/src/bin/*.rs`
relies on integration-level checks (Lean cite + decimal print).  A
lightweight `#[test]` per binary asserting "first decimal of headline
output matches snapshot" would prevent silent regression when shared
helpers (decimal, nat, Q) are touched.

## 7.  Open Lean opportunities surfaced during cleanup

- `m_t/m_c ≈ 137` cross-context coincidence with 1/α_em — looks
  combinatorial (d²·ζ(2) ≈ 41, N(α_em)=41 hierarchy).  Worth a Lean
  bound theorem.
- `192 = (NS²−1)(d²−1)` for muon lifetime: trivial Nat identity,
  belongs in `MagicNumbers` or its own micro-file.
- `(2φ−1)² = d` from golden_ratio.rs — Lean has the file but no
  0-axiom Pell identity theorem yet.

## 8.  Documentation hygiene

- HANDOFF.md still claimed "31+ binaries" — actual count = 48.
- precision-matrix.md was previously misnamed `papers/PAPER5_DRAFT.md`
  (paper 5 in `papers/` is `paper5_critical_line.tex`, an unrelated
  RH paper).  Now lives under `rust-engine/docs/` as engine companion.

— last updated 2026-04-30
