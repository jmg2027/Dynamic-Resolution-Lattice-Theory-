# DRLT-213 — Research roadmap

Ranked agenda for extending the framework, organised by
leverage class.  Each item names: what's blocked on what,
estimated tractability (HIGH = mechanical, MED = needs design
+ proof, LOW = needs new theory), and which closed chapter
hosts it.

## Tier 1 — High mathematical leverage, mechanically tractable

These should close in 1–3 sessions of focused work; each
removes a conditional or stated-but-unproved gap.

### 1.1 Per-layer ψ-kernel completeness (Direction C unconditional) — CLOSED

  · **What**: prove joint ψ-kernel ⊆ `InPrimaryCupSpanPlusBoundary`
    for every `c ≥ 1`, removing the conditional in
    `codim_upper_bound_conditional`.
  · **Status (2026-05-25, this session)**: BOTH DIRECTIONS CLOSED
    unconditionally at every c.
      · EASY (`InPrimary ⊆ joint ψ-kernel`):
        `primary_cup_span_soundness_all_c` — closed previously by
        chaining `primary_cup_span_soundness_on_layer` with
        Direction B's `parametric_arbitrary_m_full_kill_capstone`.
      · HARD (`joint ψ-kernel ⊆ InPrimary`):
        `joint_psi_kernel_subset_primary` — closed this session
        in `V33EnrichedParametricDualSpanHardLift`.  Strategy:
          1. c=1 base case: 8 explicit primary cup-product generators
             (`g_1 … g_8`) span the dim-8 ψ-kernel at single-layer
             K_{3,3}.  Closed in `V33EnrichedParametricDualSpanHard`
             via the candidate-decomposition theorem
             `joint_psi_kernel_subset_primary_c1`.
          2. ∀c lift: `promote_face`/`promote_edge` lift each c=1
             InPrimary witness to layer m of `InPrimary c`,
             preserved inductively across all 5 constructors plus
             the new `cong` constructor (closure under pointwise
             equality, added to bridge function-vs-pointwise
             without using `funext`).  `xor_aggregate` over
             m ∈ Fin c composes the layer-m promotes into a full
             reconstruction of v.
  · **Anchor**: `lean/E213/Lib/Math/Cohomology/Bipartite/V33EnrichedParametricDualSpanHard.lean`
    (c=1 base, 51 PURE) and
    `lean/E213/Lib/Math/Cohomology/Bipartite/V33EnrichedParametricDualSpanHardLift.lean`
    (c-lift + unconditional capstones, 21 PURE).
  · **Closes**: `codim = c` UNCONDITIONAL at every Stern-Brocot
    position.  `parametric_dual_span_unconditional` and
    `codim_upper_bound_unconditional` discharge the
    `H_kernel_in_span` hypothesis of the conditional capstones.

### 1.2 Arity `c = 2` Lean theorem — CLOSED

  · **What**: prove "binary is the unique non-degenerate combine
    arity" — the missing 4th piece of the atomic signature
    forcing chain.
  · **Status (2026-05-25, this session)**: CLOSED.
    `lean/E213/Theory/Atomicity/CombinatorialArity.lean` (5 PURE)
    proves the **uniform pigeonhole** `pigeonhole_fin_to_fin2`:
    any function `f : Fin k → Fin 2` with `k ≥ 3` has a collision.
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
  · **Closes**: atomic signature forcing fully formalised at Lean
    level — 4 of 4 dimensions (NS = 3 + NT = 2 via PairForcing,
    d = 5 via OrbitForcing + Five, c = 2 via this file).

### 1.3 Pell-orbit cohomology extension — CLOSED

  · **What**: verify `master_Knn_c_counter_resolved`'s universal
    framework transports to (8, 5), (5, 4), (7, 4), (13, 8) —
    the next Stern-Brocot layer.
  · **Status (2026-05-26)**: ALL FOUR CLOSED.
      · **K_{5, 4}** — closed via `K54_c_independent_h2_classes_via_framework`
        (NT=5 odd) and re-exported `K54_via_KNS4` (NT=4 even).
      · **K_{8, 5}** — closed via `kills_delta1_KNS5 8 c pairEnum8`
        (NT=5 odd route; `pairEnum8`).
      · **K_{7, 4}** — closed via `KNS4_c_independent_h2_classes 7 c
        (by decide) pairEnum7` (NT=4 even excl-T route; `pairEnum7`).
      · **K_{13, 8}** — closed via `KNS8_c_independent_h2_classes 13 c
        (by decide) pairEnum13` (NT=8 even excl-T route; new
        `psi_excl_T0_NT8` family with 21-fold XOR + 7-bool
        case-bash; new `pairEnum13` for NS=13).
  · **Anchor**: `lean/E213/Lib/Math/Cohomology/Bipartite/Parametric/PellOrbitInstances.lean`
    + `EnrichedKNSNTcEvenEven.lean` §13.5–§14 (NT=8 family).
  · **Closes**: Direction A generalises beyond `K_{n, n}` for
    `n ∈ {3, 4, 5, 6}` — all four Stern-Brocot mediant positions
    of the next layer verified.

### 1.4 α_em Step 5 capstone purity confirmation — CLOSED (already)

  · **What**: confirm `GramStructuralCapstone` +
    `invAlphaEm_precision_theorem` build as PURE, removing the
    self-referential bootstrap in Steps 3–4 (which use
    observed α on RHS).
  · **Status (2026-05-25, audit this session)**: already CLOSED.
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
  · **Closes**: α_em precision result HAD ALREADY graduated to
    "structurally forced" status — this session's only action was
    the verification audit.

## Tier 2 — Cross-chapter integration gaps (HIGH narrative leverage)

These connect already-closed programmes that currently sit
without explicit cross-reference.  Each fills a missing
chapter section, not a missing theorem.

### 2.1 Hodge involution ↔ universe-chain self-pointing — **CLOSED**

  · **Resolved 2026-05-26**: Cross-references added in both
    `hodge_conjecture.md` (§(iii) HC_Involution) and
    `universe_chain.md` (§Eisenstein discovery).  The duality
    between `⋆⋆ = id` and `1 + ω + ω² = 0` is now explicitly
    narrated as a shared self-cancelling complement structure
    driven by NS = 3.

### 2.2 Cayley-Dickson Type C ↔ Möbius P mod-3 — **CLOSED**

  · **Resolved 2026-05-26**: Cross-references added in both
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

### 2.4 Geometrization Sym(3) ↔ K_{3, 2} Sym(3) spine

  · **Gap**: `geometrization_conjecture.md` Step 24 names the
    8-geometries Sym(3) decomposition (3 isotropic + 5
    anisotropic = 2 fixed + 3 standard).  `c3_chain.md` proves
    the same `2·trivial ⊕ 3·standard` decomposition on
    H¹(K_{3, 2}^{(c=2)}).  Connection observed but not stated
    as a theorem.
  · **Action**: write explicit cross-frame theorem
    "Sym(3)-spine unification" naming both decompositions and
    the gluon-octet isomorphism that connects them.
  · **Tractability**: MED (the Lean isomorphism may need a
    new bridge file).

### 2.5 N_gen and the c-counter

  · **Gap**: `Simplex/SubInventory` derives `N_gen = 3` from
    Δ⁴ sub-face count; the c-counter layers in
    `k_nm_c_classification.md` use a different mechanism.
    Currently these are independent.
  · **Action**: investigate whether `N_gen` and per-layer
    c-counter share a deeper Stern-Brocot / Pell origin.  If
    yes, write the bridge.  If no, document the layer at which
    each operates within the same residue (Δ⁴ sub-face count vs.
    enriched cohomology block index) — not as a substrate/
    superstructure split.
  · **Tractability**: LOW–MED (research question).

## Tier 3 — Narrative depth deficits (chapter-local)

Sections that are PROVABLE in Lean but UNEXPLAINED in chapter
narrative.  Readers can verify but not understand.

### 3.1 ψ-discriminator WHY (Cohomology) — **CLOSED**

  · **Resolved 2026-05-26**: `k_nm_c_classification.md`
    now leads the c-counter narrative with the enriched
    direct-sum decomposition
    `C¹_enr = ⊕_{m ∈ Fin c} C¹_simple_m`,
    `C²_enr = ⊕_{m ∈ Fin c} C²_simple_m`, and then explains
    `9·m` cancellation as the proof-level shadow of that
    disjoint-layer translation symmetry.  The ψ-functional is
    now motivated structurally before technical lemmas.

### 3.2 PRIMARY cup-image naturality

  · **Gap**: `k_nm_c_classification.md` §"Why PRIMARY (not
    FULL) cup-image" states the technical reason (bilinearity
    fills `EnrichedFaceVal` entire) but not the structural
    one.  Is `InPrimaryCupSpanPlusBoundary` the **unique
    maximal** kill-preserving cup-image restriction?
  · **Action**: prove the maximality claim, or rewrite the
    section to drop the naturality framing and present
    PRIMARY as a specific design choice.

## Tier 4 — Physics deployment extensions

### 4.1 Catalog ↔ Lean parity audit — **CLOSED**

  · **Resolved 2026-05-26**: All 6 "remaining" observables
    (Koide, m_p/m_e, M_Pl/v_H, muon 192, m_t/m_c, η_B)
    confirmed to have PURE falsifiers in Lean (F21–F26).
    `catalogs/physics-constants.md` updated: Phase 5 → Phase 6,
    23/23 paired = 100% coverage.

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
  · **Action**: deploy the mediant-functor machinery from
    `mediant_cohomology_functor.md` to generate
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
  · **Progress (2026-05-26)**: added
    `lean/E213/Lib/Math/SimplexCountsBridge.lean` and migrated
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

  · **Gap**: `lean/E213/Lib/Math/PatternCatalog/` (6 files,
    ~500 SLOC) has no `theory/math/` chapter.  Violates
    promotion parity.
  · **Action**: write `theory/math/pattern_catalog.md`.

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

All Tier 1 items are CLOSED (1.1, 1.2, 1.3, 1.4).
Tier 2.1, 2.2, and Tier 4.1 are CLOSED (2026-05-26).
The next-shot focus should be one of:

  · **Tier 2.3 p-adic_real213 ↔ Möbius P mod-p periods** — MED
    narrative leverage, extends the mod-p ↔ p-adic Lens
    correspondence.
  · **Tier 5.1 propext unsealing** — MED hygiene, converts
    ~20 DIRTY theorems to PURE.

## Inter-item dependencies

  · **1.1 SATISFIED (closed 2026-05-25)**: `codim = c` is now
    unconditional at every c via
    `joint_psi_kernel_subset_primary` +
    `parametric_dual_span_unconditional`.  Downstream updates
    applied: `theory/math/cohomology/k_nm_c_classification.md`
    overview + key-results + open frontier; STATE.md c-counter
    row.  Follow-on essay update in
    `theory/essays/c_counter_programme_closure.md` still
    pending.
  · **1.2 SATISFIED (closed 2026-05-25)**: atomic forcing chain
    (NS, NT, d, c) = (3, 2, 5, 2) is now fully Lean-formalised
    via `CombinatorialArity.arity_2_unique_via_k_ge_3_vacuous`
    (parametric ∀ k ≥ 3 pigeonhole over `Fin 2` base).  Downstream
    update applied to `STATE.md` Closed table; chapter
    `physics/foundations/atomic_constants.md` already noted "all
    four forced" via the narrative chain.
  · **1.3 SATISFIED (closed 2026-05-26)**: all four Pell-orbit
    pairs closed — K_{5, 4}, K_{7, 4}, K_{8, 5}, K_{13, 8} via
    KNS4 / KNS5 / KNS8 routes.  The NT=8 `psi_excl_T0_NT8`
    family + `pairEnum13` completed the extension.  Capstone
    `pell_orbit_stern_brocot_extension_capstone` bundles 4/4.
  · **Tier 2.1 CLOSED (2026-05-26)**: Hodge ↔ universe-chain.
  · **Tier 2.2 CLOSED (2026-05-26)**: Cayley-Dickson ↔ Möbius.
  · **Tier 4.1 CLOSED (2026-05-26)**: catalog 23/23 paired.
  · **2.4 (Sym(3)-spine unification) needs** a new bridge file
    if the gluon-octet ↔ 8-geometries isomorphism is to live in
    Lean rather than only narrative — likely under
    `lean/E213/Lib/Physics/Symmetry/` cross-cited from
    `lean/E213/Lib/Math/GeometrizationConjecture/`.
  · **5.1 cleans ⇒** unlocks safe motion of 1.1's anchor file
    if any Math/Physics import-graph entanglement surfaces
    during the per-layer completeness work.

## Anti-goals (what this plan is NOT)

Per `CLAUDE.md` Failure modes catalog, these slips are out of
scope and should not appear in any item's "Action":

  · Comparison-frame import (e.g. "213 vs classical cohomology",
    "Stern-Brocot vs Farey").  213-native operational primitives
    only.
  · Stereotype matching ("this corresponds to standard math
    X") in chapter narrative.
  · Substrate/superstructure framing (Tier 2.5 wording fix
    applies repo-wide; same caution for 5.1 "Math context vs
    Physics context" — they are bounded-context labels, not
    layered ontologies).
  · Forcible map onto existing physics in Tier 4 items —
    numerical disagreement is a missing-physics signal, not a
    target to fit.

## Cross-references

  · `theory/STATE.md` — current framework state and headline
    closures
  · `theory/INDEX.md` — book map
  · `HANDOFF.md` — volatile session state
  · `research-notes/G35_chiral_cup_ring_catalog.md` — per-
    conjecture catalog (active scratch)
  · `theory/essays/c_counter_programme_closure.md` — Tier-1
    items 1.1–1.3 anchor essay
  · `theory/essays/p_orbit_closure_master.md` — Tier-2 item
    2.3 anchor essay
  · `theory/essays/synthesis_interlock_map.md` — the c-counter
    ↔ P-orbit ↔ layer-multiplication correspondence
