# DRLT-213 — Research roadmap

Ranked agenda for extending the framework, organised by
leverage class.  Each item names: what's blocked on what,
estimated tractability (HIGH = mechanical, MED = needs design
+ proof, LOW = needs new theory), and which closed chapter
hosts it.

## Tier 1 — High mathematical leverage, mechanically tractable

These should close in 1–3 sessions of focused work; each
removes a conditional or stated-but-unproved gap.

### 1.1 b₀/b₁/b₂ Betti structure at K_{3,2}^{(c=2)} — CLOSED

  · **What**: pin the cohomology Betti numbers of the canonical
    filled graph — connectedness across the family and the
    filled-3-cell anchor.
  · **Status**: CLOSED.
      · `b₀ = 1` (connectedness) for every `K_{NS,NT}^{(c)}`:
        `KernelConstancyUniversal.universal_kernel_close`.
      · `b₁ = 6`, `b₂ = 1` at the K_{3,2}^{(c=2)} filling:
        `Filled3CellCohomology.phase1_cohomology_anchor`, with the
        generating relation `Filled3CellCohomology.face_dependence`
        (`Face₀ ⊕ Face₁ ⊕ Face₂ = 0`).
      · `b₁ = 8 = NS² − 1` gluon-octet reading:
        `GluonChannelInterpretation.eight_fold_QCD_identification`.
  · **Anchor**:
    `lean/E213/Lib/Math/Cohomology/Bipartite/Parametric/Betti/KernelConstancyUniversal.lean`,
    `lean/E213/Lib/Math/Cohomology/Bipartite/Filled3CellCohomology.lean`,
    `lean/E213/Lib/Physics/Symmetry/GluonChannelInterpretation.lean`.
  · **Closes**: the Betti structure of the canonical lattice graph
    is fixed in Lean, with the connectedness statement holding
    uniformly across the whole `K_{NS,NT}^{(c)}` family.

### 1.2 Arity `c = 2` Lean theorem — CLOSED

  · **What**: prove "binary is the unique non-degenerate combine
    arity" — the missing 4th piece of the atomic signature
    forcing chain.
  · **Status**: CLOSED.
    `lean/E213/Theory/Atomicity/CombinatorialArity.lean` (5 PURE)
    proves the **uniform pigeonhole** `pigeonhole_fin_to_fin2`:
    any function `f: Fin k → Fin 2` with `k ≥ 3` has a collision.
    Generic parametric `Raw k` and `Reachable k` (with Fin-k arity
    `rel` requiring pairwise-distinct args) define a uniform family;
    `reachable_only_object` shows that for every `k ≥ 3`, the
    `rel` step constructor never fires (no Reachable rel-term).
    Capstone `arity_2_unique_via_k_ge_3_vacuous` packages the
    "k = 2 is structurally unique" claim parametrically.
    Companion to `ArityForcing.lean` (k = 3 explicit) — this file
    is the ∀ k ≥ 3 generalization.
  · **Anchor**: `lean/E213/Theory/Atomicity/CombinatorialArity.lean`
    (5 PURE).
  · **Closes**: atomic signature forcing formalised at Lean level —
    the forced atoms `(NS, NT, d) = (3, 2, 5)` (NS = 3 + NT = 2 via
    PairForcing, d = 5 via OrbitForcing + Five).  `CombinatorialArity`
    forces the relation **arity = 2**, a distinct quantity from the edge
    multiplicity `c`; `c = 2` is a posited presentation parameter
    (`atomic_c_multiplicity_forcing.md`), not a fourth forced dimension.

### 1.3 α_em Step 5 capstone purity confirmation — CLOSED (already)

  · **What**: confirm `GramStructuralCapstone` +
    `invAlphaEm_precision_theorem` build as PURE, removing the
    self-referential bootstrap in Steps 3–4 (which use
    observed α on RHS).
  · **Status**: already CLOSED.
    `lean/E213/Lib/Physics/AlphaEM/GramStructuralCapstone.lean`
    scans **7 PURE / 0 DIRTY** including
    `invAlphaEm_precision_theorem` at line 133.  The theorem
    explicitly carries (a) the 5-layer base formula coefficients,
    (b) `gram_correction_structural = 2130` derived via Newton-1
    from `y₀ = X` on the cubic `25y³ + 1 = 25Xy²` using ONLY
    `alphaInv_213_e9` on RHS (no observed α), and (c) the
    numerical match `alphaInv_structural_e9 = 137035999111`
    structural vs CODATA `137035999084` → 27 × 10⁻⁹ ≈ 0.2 ppb
    residual.  All seven theorems certified PURE by
    `scan_axioms.py`.
  · **Anchor**: `lean/E213/Lib/Physics/AlphaEM/GramStructuralCapstone.lean`
    (7 PURE).
  · **Closes**: the α_em precision result is at "structurally forced"
    status (verified).

## Tier 2 — Cross-chapter integration gaps (HIGH narrative leverage)

These connect already-closed programmes that currently sit
without explicit cross-reference.  Each fills a missing
chapter section, not a missing theorem.

### 2.1 Hodge involution ↔ universe-chain self-pointing — **CLOSED**

  · **Resolved**: Cross-references added in both
    `hodge.md` (⋆⋆ = id involution) and
    `universe_chain.md` (§Eisenstein discovery).  The duality
    between `⋆⋆ = id` and `1 + ω + ω² = 0` is now explicitly
    narrated as a shared self-cancelling complement structure
    driven by NS = 3.

### 2.2 Cayley-Dickson Type C ↔ Möbius P mod-3 — **CLOSED**

  · **Resolved**: Cross-references added in both
    `mobius213_p_orbit_closure.md` (after P-orbit table) and
    `algebra_tower.md` (after Type C row).  The factorisation
    `L(3) = 18 = NS · |ℤ[ω]×|` and the mod-3 period `4 = NT²`
    encoding `Z_6 / Z_2` index are now explicitly linked.

### 2.3 p-adic_real213 ↔ Möbius P mod-p periods

  · **Gap**: `padic_real213.md` constructs ℤ_p / ℚ_p for any
    prime p.  `mobius213_p_orbit_closure.md` catalogs mod-p
    periods of P in `GL(2, F_p)`.  No analytic bridge between
    p-adic valuation and the period sequence.
  · **Action**: add §"p-adic Lens of mod-p periods" stating
    `D(p) = O(log p)` follows from valuation-theoretic
    bounds on Teichmüller lifting.
  · **Tractability**: MED (sketches the conjecture; Lean proof
    is separate).

## Tier 3 — Narrative depth deficits (chapter-local)

Sections that are PROVABLE in Lean but UNEXPLAINED in chapter
narrative.  Readers can verify but not understand.  No open
items at present.

## Tier 4 — Physics deployment extensions

### 4.1 Catalog ↔ Lean parity audit — **CLOSED**

  · **Resolved**: All 6 "remaining" observables
    (Koide, m_p/m_e, M_Pl/v_H, muon 192, m_t/m_c, η_B)
    confirmed to have PURE falsifiers in Lean (F21–F26).
    `catalogs/physics-constants.md`: 23/23 paired = 100% coverage.

### 4.2 Hadron baryon spectrum

  · **Gap**: `theory/physics/hadron.md` has falsifier brackets
    (`m_t/m_c ∈ [130, 145]`) but no first-principles channel-sum
    formula for baryon masses.  `lean/E213/Lib/Physics/Hadron/`
    currently houses `ProtonMass`, `ProtonElectronRatio`,
    `Bigrading`, `Bridge` — no baryon channel-sum file.
  · **Action**: add `lean/E213/Lib/Physics/Hadron/BaryonMass.lean`
    with the channel-sum analogue of the α_em five-layer
    decomposition.
  · **Tractability**: MED.

### 4.3 CKM full matrix

  · **Gap**: Cabibbo λ = 5/22 = d/(d² − NS) is closed in
    catalog.  Remaining 8 CKM parameters are open.
  · **Action**: derive the remaining mixing angles from the
    Stern-Brocot mediant positions of the atomic signature
    (`Mobius213SternBrocot`) to generate
    `θ_12, θ_23, θ_13, δ_CP`.
  · **Tractability**: MED.

### 4.4 P-orbit naturalness operationalised in physics

  · **Gap**: P-orbit naturalness boundary is closed on the
    math side; not used in any physics derivation.  No mass
    ratio is currently shown to factor through L(k) or any
    Pell-Fibonacci orbit.
  · **Action**: investigate which physics observables are
    L(k)-derivable; close the first concrete one as a precision
    theorem.
  · **Tractability**: MED–LOW.

### 4.5 Chapters below Validation Standard

  · Mass, Mixing, Nuclear, Quantum, Higgs, Basel chapters
    have PURE Lean content but no independent precision
    ≥ ppb-ppm or falsifier.
  · **Action**: per chapter, either (a) close a Standard-meeting
    result, (b) mark the chapter as a *component* of a
    higher-level result (e.g. Basel feeds α_em), or (c) demote
    to `research-notes/`.

## Tier 5 — Architectural / tooling (longer horizon)

### 5.1 Math ↔ Physics bridge discipline

  · **Gap**: cross-context imports under `lean/E213/Lib/`
    currently total **174 Math → Physics + 56 Physics → Math**
    direct `import E213.Lib.{...}` lines.  Bounded-context spec
    lives in `lean/E213/ARCHITECTURE.md` §1 "Lib/" subsection
    (Math + Physics as two bounded contexts) and §3 "Bridge.lean
    for cross-context".
  · **Current state**: 40 `*Bridge*.lean` files already
    instantiate the anti-corruption-layer pattern across both
    contexts; the pattern is established but unevenly applied —
    many Math files still import `E213.Lib.Physics.*` directly
    without going through a Bridge shim.
  · **Progress**: added
    `lean/E213/Lib/Math/Foundations/SimplexCountsBridge.lean` and migrated
    three Math files (`ParadigmDomainGraded`,
    `Mobius213/Px/IterationSpecies`,
    `Mobius213/Px/DecompositionCatalog`) to import the Math-side
    bridge instead of `E213.Lib.Physics.Simplex.Counts` directly.
  · **Action**: audit each direct cross-context import; route
    through (or create) the corresponding `Bridge.lean`.  Goal:
    every cross-context citation grep-discoverable via
    `*Bridge*.lean`.
  · **Tractability**: MED (mechanical move per file; needs
    coordinated import-graph audit; existing 40 Bridge files
    give the naming template).

### 5.2 Methodology meta-files consolidation

  · **Gap**: `theory/meta/` currently holds 7 non-INDEX files —
    `methodology_patterns`, `pure_lean_patterns`,
    `multiplicity_doctrine`, `raw_derivation_levels`,
    `scanner_suite`, `cardinality_cutoff_principle`,
    `cardinality_cutoff_applications` — with topical overlap
    across the first three and between the two
    `cardinality_cutoff_*` files.
  · **Action**: merge `pure_lean_patterns` +
    `multiplicity_doctrine` into a new
    `theory/meta/architectural_patterns.md`; fold the two
    `cardinality_cutoff_*` files into a single
    `cardinality_cutoff.md` (principle + application examples in
    one chapter); move `scanner_suite` to
    `tools/scanner_suite.md`; trim `methodology_patterns.md` to
    ≤800 lines.

### 5.3 PatternCatalog/Lib/Math/ promotion

  · **Gap**: `lean/E213/Lib/Math/Foundations/PatternCatalog/` (6 files,
    ~500 SLOC) has no `theory/math/` chapter.  Violates
    promotion parity.
  · **Action**: write `theory/math/foundations/pattern_catalog/pattern_catalog.md`.

### 5.4 Catalog ↔ Lean verification tool

  · **Gap**: `catalogs/` is described as "ground truth ← Lean
    theorems" but no automated checker.  Catalog drift
    possible.
  · **Action**: write `tools/verify_catalogs.py` that extracts
    constants from Lean and compares against catalog claims.
    Add to CI step.

### 5.5 Sealed-DIRTY unsealing opportunity (SemanticAtom)

  · **Gap**: 23 propext-sealed theorems in
    `Lens/SemanticAtom.lean` could be unsealed by switching
    codomain from `Prop` to `Bool`.  STRICT_ZERO_AXIOM.md
    sealing narrative reads structural; analysis shows it is
    pragmatic.
  · **Action**: refactor and convert ~20 DIRTY → PURE.

## Priority ranking (one-shot session leverage)

All Tier 1 items are CLOSED (1.1, 1.2, 1.3).
Tier 2.1, 2.2, and Tier 4.1 are CLOSED.
The next-shot focus should be one of:

  · **Tier 2.3 p-adic_real213 ↔ Möbius P mod-p periods** — MED
    narrative leverage, extends the mod-p ↔ p-adic Lens
    correspondence.
  · **Tier 4.2 Hadron baryon spectrum** — MED deployment leverage,
    first channel-sum extension under `Lib/Physics/Hadron/`.

## Inter-item dependencies

  · **1.1 SATISFIED (closed)**: the Betti structure at
    K_{3,2}^{(c=2)} is fixed — `b₀ = 1` uniformly via
    `KernelConstancyUniversal.universal_kernel_close`, `b₁ = 6`
    and `b₂ = 1` via `Filled3CellCohomology.phase1_cohomology_anchor`,
    `b₁ = 8 = NS² − 1` gluon octet via
    `GluonChannelInterpretation.eight_fold_QCD_identification`.
  · **1.2 SATISFIED (closed)**: atomic forcing chain
    `(NS, NT, d) = (3, 2, 5)` (with `c` a derived presentation
    parameter, not a fourth forced primitive) is now fully
    Lean-formalised via
    `CombinatorialArity.arity_2_unique_via_k_ge_3_vacuous`
    (parametric ∀ k ≥ 3 pigeonhole over `Fin 2` base, forcing the
    relation arity = 2).  Downstream update applied to `STATE.md`
    Closed table; chapter `physics/foundations/atomic_constants.md`
    notes the forced atoms via the narrative chain.  `(NS, NT)`
    forced and `c` not forced is anchored in
    `AtomicConstantsParametricFullIff.c2b_full_iff`.
  · **Tier 2.1 CLOSED**: Hodge ↔ universe-chain.
  · **Tier 2.2 CLOSED**: Cayley-Dickson ↔ Möbius.
  · **Tier 4.1 CLOSED**: catalog 23/23 paired.
  · **5.1 cleans ⇒** unlocks safe motion of the cohomology
    anchor files if any Math/Physics import-graph entanglement
    surfaces during further cohomology work.

## Anti-goals (what this plan is NOT)

Per `CLAUDE.md` Failure modes catalog, these slips are out of
scope and should not appear in any item's "Action":

  · Comparison-frame import (e.g. "213 vs classical cohomology",
    "Stern-Brocot vs Farey").  213-native operational primitives
    only.
  · Stereotype matching ("this corresponds to standard math
    X") in chapter narrative.
  · Substrate/superstructure framing (applies repo-wide; same
    caution for 5.1 "Math context vs Physics context" — they are
    bounded-context labels, not layered ontologies).
  · Forcible map onto existing physics in Tier 4 items —
    numerical disagreement is a missing-physics signal, not a
    target to fit.

## Cross-references

  · `theory/STATE.md` — current framework state and headline
    closures
  · `theory/INDEX.md` — book map
  · `HANDOFF.md` — volatile session state
    conjecture catalog (active scratch)
  · `theory/essays/p_orbit/p_orbit_closure_master.md` — Tier-2 item
    2.3 anchor essay
  · `theory/essays/synthesis/the_forcing_criterion_is_distinguishing.md`
    — the forcing-criterion synthesis essay
