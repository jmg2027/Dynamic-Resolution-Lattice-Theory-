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

### 1.3 Pell-orbit cohomology extension — PARTIALLY CLOSED

  · **What**: verify `master_Knn_c_counter_resolved`'s universal
    framework transports to (8, 5), (5, 4), (7, 4), (13, 8) —
    the next Stern-Brocot layer.
  · **Status (2026-05-25, this session)**: Three of four CLOSED;
    (13, 8) deferred.
      · **K_{5, 4}** — closed via `K54_c_independent_h2_classes_via_framework`
        (NT=5 odd) and re-exported `K54_via_KNS4` (NT=4 even).
      · **K_{8, 5}** — closed via `kills_delta1_KNS5 8 c pairEnum8`
        (NT=5 odd route; new `pairEnum8` added).
      · **K_{7, 4}** — closed via `KNS4_c_independent_h2_classes 7 c
        (by decide) pairEnum7` (NT=4 even excl-T route; new
        `pairEnum7` added).
      · **K_{13, 8}** — both NS=13 (odd, ∉ {3, 5}) and NT=8
        (even, ∉ {4, 6}) outside current family coverage.  Needs
        either `pairEnum13` + `IsLexFold` proof (then NS=13
        universal-S route closes) OR fresh `psi_excl_T0_NT8`
        + 28-fold XOR cancellation (then NT=8 family closes).
        Both routes mechanical; deferred to next session.
  · **Anchor**: `lean/E213/Lib/Math/Cohomology/Bipartite/Parametric/PellOrbitInstances.lean`
    (11 PURE — pairEnum7, pairEnum8, three pair closures + capstone
    `pell_orbit_stern_brocot_extension_capstone`).
  · **Closes**: empirical confidence that Direction A truly
    generalises beyond `K_{n, n}` for `n ∈ {3, 4, 5, 6}` — three
    Stern-Brocot mediant positions verified.

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

### 2.1 Hodge involution ↔ universe-chain self-pointing

  · **Gap**: `theory/math/cohomology/hodge_conjecture.md`
    closes HC on K_{3, 2}^{(c=2)}; `theory/math/universe_chain.md`
    Step 19 frames the same Hodge involution as
    *complement-cochain self-pointing*.  Neither chapter cites
    the other on this point.
  · **Action**: add §"Hodge involution as self-pointing" to
    `hodge_conjecture.md` Foundation; mutual cross-reference.
  · **Tractability**: HIGH (narrative only).

### 2.2 Cayley-Dickson Type C ↔ Möbius P mod-3

  · **Gap**: `theory/math/cayley_dickson/algebra_tower.md`
    Type C uses `ZOmega = ℤ[ω]` (cube root of unity, intrinsically
    3-adic).  `theory/math/mobius213_p_orbit_closure.md` mod-3
    period is 4 = `NT²` and L(3) = 18.  The 3-adic structure
    on both sides is the same generative phenomenon.
  · **Action**: add §"Eisenstein discovery at k = 3" to
    `mobius213_p_orbit_closure.md` linking L(3) = 18 to ZOmega
    L3 Dickson group; converse cross-reference in
    `algebra_tower.md` Type C.
  · **Tractability**: HIGH (narrative only).

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

### 3.1 ψ-discriminator WHY (Cohomology)

  · **Gap**: `k_nm_c_classification.md` §"ψ-discriminator
    as universal block functional" defines the functional and
    proves its properties, but does not motivate the `9·m`
    offset structure as the algebraic shadow of disjoint-layer
    direct-sum.  Reader can verify; cannot understand.
  · **Action**: rewrite the section to lead with the direct-sum
    decomposition `C¹_enr = ⊕_m C¹_simple_m` and present the
    9-block index structure as its shadow.

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

### 4.1 Catalog ↔ Lean parity audit (MED priority)

  · **Status**: `m_p/m_e ≈ 6π⁵` is closed at
    `lean/E213/Lib/Physics/Hadron/ProtonElectronRatio.lean`
    (precision + falsifier; cross-cited in
    `Lib/Physics/Hadron/Bigrading.lean:149`).
    `M_Pl/v_H = d^(d²) / (d+1) = 5²⁵ / 6` is closed at
    `lean/E213/Lib/Physics/Mass/HierarchyTowers.lean` +
    `lean/E213/Lib/Physics/Higgs/Vacuum.lean:78–86` (precision +
    falsifier).
  · **Real gap**: `catalogs/physics-constants.md` line 73 still
    lists these two among "Remaining 6 ... precision side only;
    falsifier side is the next extension target".  Catalog is
    stale relative to Lean.
  · **Action**: audit the "Remaining 6" line against current
    falsifier coverage (`catalogs/falsifiers.md` F1–F20); update
    catalog to reflect actual paired status; check the four
    untouched (Koide 2/3, η_B, m_t/m_c, muon prefactor 192) for
    falsifier presence and split accordingly.
  · **Tractability**: HIGH (catalog grep + cross-check).

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

All four Tier 1 items are now CLOSED (1.1, 1.2, 1.4 fully;
1.3 partially — K_{13, 8} still mechanical-deferred).  The
next-shot focus should be one of:

  · **K_{13, 8}** (Tier 1.3 residue) — pairEnum13 + IsLexFold
    OR psi_excl_T0_NT8 + 28-fold XOR.  Mechanical.
  · **Tier 2.1 Hodge ↔ universe-chain** — HIGH narrative
    leverage, no Lean needed.
  · **Tier 4.1 Catalog ↔ Lean parity audit** — HIGH hygiene
    sweep.

If choosing one tier-2 cross-reference: **2.1 Hodge ↔
universe-chain self-pointing**.  Highest narrative coherence
gain for least effort.

If choosing one tier-4 hygiene: **4.1 catalog ↔ Lean parity
audit**.  Catalog text lags actual Lean coverage; cheap to
sweep.

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
  · **1.3 PARTIALLY SATISFIED (closed 2026-05-25)**: three of
    four pairs closed — K_{5, 4}, K_{7, 4}, K_{8, 5} via the
    KNS4 / KNS5 routes plus new pairEnum7 / pairEnum8.  Direction
    A's generalisation beyond `K_{n, n}` for `n ∈ {3, 4, 5, 6}`
    is empirically confirmed at three Stern-Brocot mediant
    positions.  Only K_{13, 8} remains — requires `pairEnum13` +
    IsLexFold OR `psi_excl_T0_NT8` (both mechanical).  Downstream
    feed-into 2.3 (p-adic Lens of mod-p periods) still applicable
    once K_{13, 8} closes.
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
