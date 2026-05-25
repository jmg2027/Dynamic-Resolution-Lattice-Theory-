# Session handoff

Branch: `claude/tier-1-1-psi-kernel-wnpIS` (merged with main's
unified-math-foundation work).  Built clean
(`cd lean && lake build`), 0 sorry, 0 external axioms.  Full
project: 181 PURE / 0 DIRTY on production critical path.
`E213.Lens.Unified` scans 14 PURE / 0 DIRTY (main).
`V33EnrichedParametricDualSpanHard` + `…HardLift` scan 72 PURE / 0
DIRTY (this branch).

## This session — combined

Two parallel closures merged into one branch:

### Tier 1.1 — Per-layer ψ-kernel completeness, FULLY CLOSED at every c ≥ 1

  · HARD direction at c=1: 8 explicit primary cup-product
    generators `g_1 … g_8` spanning the dim-8 ψ-kernel at
    single-layer K_{3,3}.  Generators are cups of `starS`/
    `incidT` cocycles with single-edge cochains (`e_edge`).
    Closed-form decomposition coefficients `b_1 … b_8`
    extracted from v's 9 face values; the (1, 0) position
    equation `v(1,0) = b_3 ⊕ b_4 ⊕ b_7 ⊕ b_8` is exactly
    `ψ_0(v) = 0`.  9 per-position lemmas verify pointwise
    equality; `cong` constructor (added to the `InPrimary`
    inductive) bridges to v as a function without `funext`.
    `joint_psi_kernel_subset_primary_c1` in
    `V33EnrichedParametricDualSpanHard` (51 PURE).
  · ∀c lift via layer-promotion: `promote_face`/`promote_edge`
    (9-fold `cond` cascade — propext-free) transport each c=1
    InPrimary witness to layer m of `InPrimary c`.  Preserved
    across all 6 constructors (zero, coboundary, starCup,
    incidCup, xor_add, cong) inductively.  `xor_aggregate`
    composes layer-m promotes into a full reconstruction of v.
    `joint_psi_kernel_subset_primary` and unconditional
    capstones (`parametric_dual_span_unconditional`,
    `codim_upper_bound_unconditional`) in
    `V33EnrichedParametricDualSpanHardLift` (21 PURE).
  · `codim = c` upper bound is now UNCONDITIONAL at every
    Stern-Brocot position against the PRIMARY cup-image.

### Unified-equivalence synthesis (from main)

Defined the 213-native concept that subsumes equivalence,
equivalence class, isomorphism, and homomorphism (동치 / 동치류 /
동형 / 준동형) as the **Lens-arrow** (= `Lens.refines L M`).

  · `theory/lens/unified_equivalence.md` — synthesis chapter.
    Single-concept thesis, four classical readings as
    decompositions, canonical-form ladder `cutEq ⇒
    sternBrocotEq ⇒ mobiusEq` via Möbius P = [[2, 1], [1, 1]],
    Eqv ↔ Lens.equiv collapse, axiom-cost table.
  · `theory/lens/dirty_recovery_patterns.md` — methodology
    chapter built on top of the unification.  Four named
    patterns (P1: Lens-Eq → LensIso, P2: mutual morphism →
    LensIso, P3: classical quotient → LensImage, P4: slash-cong
    assertion → kernel inheritance) for converting DIRTY claims
    into PURE Lens-arrow statements.
  · `lean/E213/Lens/Unified.lean` (14 PURE) — `LensIso`,
    `LensFiber`, recovery bridges (`lensIso_of_eqPW`,
    `lensIso_of_morphism_pair`, `LensImage`).

### Cross-link between the two work streams

The `cong` constructor on `InPrimaryCupSpanPlusBoundary` (Tier
1.1) is structurally parallel to Pattern P1 of
`dirty_recovery_patterns.md`: both use pointwise equality as the
bridge to avoid `funext`.  P1 operates at the Lens level
(Lens-Eq → LensIso via `eqPW`); the cong constructor lifts the
same idea to **arbitrary inductive predicates on function
types**.  See `theory/essays/per_layer_completeness_constructive_closure.md`
§"The `cong` constructor as funext-bypass" +
`theory/essays/pure_funext_avoidance.md` 5th pattern.

### Tier 1.3 — Pell-orbit Stern-Brocot mediant extension, 3/4 closed

Three of the four next-Stern-Brocot-layer pairs from the
research plan are now closed:

  · K_{5, 4} via `K54_via_KNS4` (NT=4 excl-T route)
  · K_{7, 4} via `K74_c_independent_h2_classes_via_framework`
    (NT=4 excl-T route, new `pairEnum7`)
  · K_{8, 5} via `K85_c_independent_h2_classes_via_framework`
    (NT=5 odd qT-zero route, new `pairEnum8`)
  · Capstone: `pell_orbit_stern_brocot_extension_capstone`

11 PURE in `Parametric/PellOrbitInstances.lean` (new file).

Only K_{13, 8} remains — both NS=13 odd ∉ {3, 5} and NT=8 even
∉ {4, 6}.  Closes via either `pairEnum13` + IsLexFold proof
(universal-S route) OR fresh `psi_excl_T0_NT8` + 28-fold XOR
cancellation (NT=8 excl-T family).  Mechanical, deferred.

### Tier 1.2 — Arity c=2 Lean theorem, CLOSED

The 4th atomic-signature dimension (k = 2 arity) is now
Lean-formalised parametrically via
`Theory/Atomicity/CombinatorialArity.lean` (5 PURE):

  · `pigeonhole_fin_to_fin2 (k : Nat) (hk : 3 ≤ k) (f : Fin k → Fin 2)`
    — ∀ f, ∃ i ≠ j, f i = f j.  Three-index in-line case-bash via
    `cases_lt_two`, no `Classical.choice` (constructive `obtain`
    on Exists at tactic level).
  · Generic `Raw k` and `Reachable k` (k-arity `rel` with pairwise-
    distinct args).
  · `reachable_only_object`: ∀ k ≥ 3, every Reachable Raw term is
    a base object — k-arity rel never fires.
  · `arity_2_unique_via_k_ge_3_vacuous`: the structural capstone
    bundling the ∀ k ≥ 3 vacuousness.

Atomic signature `(NS, NT, c, d) = (3, 2, 2, 5)` now Lean-forced
across all 4 dimensions.  `STATE.md` Closed row + chapter
`physics/foundations/atomic_constants.md` Combined inevitability
chain extended with the c=2 row.

### Tier 1.4 — α_em Step 5 already PURE (audit only)

`lean/E213/Lib/Physics/AlphaEM/GramStructuralCapstone.lean` scans
7 PURE / 0 DIRTY including `invAlphaEm_precision_theorem` which
explicitly carries the 0.2 ppb structural derivation (cubic
`25y³ + 1 = 25Xy²`, Newton-1 from y₀ = X, ONLY `alphaInv_213_e9`
on RHS — no observed α).  Tier 1.4 retroactively closed.

## Boot order

  · `seed/AXIOM/05_no_exterior.md` §5, §8.4 — re-read every
    session start
  · `theory/lens/unified_equivalence.md` — the single-concept
    statement (start here for any equivalence / iso / hom
    question)
  · `theory/INDEX.md` — book map
  · `lean/E213/ARCHITECTURE.md` — layer ring spec
  · `theory/PROMOTION_CRITERIA.md` — Hard / Soft gates

## What's closed (chapter level)

Highlights — full list in `theory/INDEX.md`:

  · `theory/lens/unified_equivalence.md` — 동치 / 동치류 / 동형 /
    준동형 single-concept synthesis
  · `theory/lens/dirty_recovery_patterns.md` — P1-P4 toolkit for
    DIRTY → PURE recovery
  · `theory/math/cohomology/k_nm_c_classification.md` — universal
    `(NS, NT, c)` cohomology framework (EnrichedKNSNTc) +
    codim ≥ c parametric + codim ≤ c dual-span
    (**NOW unconditional at every c**) + arbitrary-m bilateral
    kill (`9·m` cancellation in `NatBeqHelpers`)
  · `theory/math/cohomology/mediant_cohomology_functor.md` —
    Stern-Brocot mediant Vandermonde at the count level (V
    2-term / E 4-term / F factored-Vandermonde²); K_{4, 3} =
    K_{1, 1} ⊕ K_{3, 2} marquee
  · `theory/math/cohomology/tripartite_self_containment.md` —
    K_{3, 2}^{(c=2)} local (2, 1, 3) signature at every point;
    K_{2, 1, 3} Betti (1, 0, 0); cohomology-level
    self-containment verdict (atomic preserved, b₁ breach)
  · `theory/math/mobius213_p_orbit_closure.md` — P-orbit
    naturalness boundary + structural forcing via
    `Theory/Atomicity/OrbitForcing` + Lucas-Pell recurrence
    + period reciprocity + n-Fibonacci + Cassini universal
  · `theory/essays/per_layer_completeness_constructive_closure.md`
    — 213-native exposition of the 8 generators + ∀c lift
  · `theory/essays/c_counter_programme_closure.md` —
    cross-cutting synthesis of the c-counter five-direction
    closure + same-shape parallel to P-orbit

## What's open (residual)

Per-layer completeness — closed (this session).
Pell-orbit extension — 3/4 closed (this session).
Genuinely open structural questions:

  · **Cochain-level mediant functor**: count-level Vandermonde
    closed; lifting to cup-product algebra (4 edge + 9 face
    sub-cells per mediant) is the next layer.
  · **Massey-class mediant lift**: do K_{4, 3} 4-fold Massey
    witnesses factor through K_{1, 1} ⊕ K_{3, 2}?
  · **K_{13, 8} extension**: only remaining Pell-orbit pair.
    Both NS=13 odd ∉ {3, 5} and NT=8 even ∉ {4, 6} outside
    current family coverage — mechanical via either pairEnum13
    + IsLexFold or psi_excl_T0_NT8 + 28-fold XOR.
  · **n-prime P-orbit depth bound**: empirically D(p) ≤ 4 for
    p ≤ 97; asymptotic growth (O(log p)?) is open.
  · **Cup-product transport on V32LocalSignature**: does the
    (2, 1, 3) local signature persist under cup
    `H^k × H^l → H^(k+l)` at K_{3, 2}^{(c=2)}?
  · **Tier 1.2 — Arity c=2 Lean theorem**: missing 4th piece
    of atomic signature forcing.
  · **Möbius reverse-direction coverage**: `mobiusEq → cutEq`
    requires Stern-Brocot total coverage of ℕ × ℕ (standard CS
    result on coprime pairs + scaling for non-coprime).  Lean
    closure open; forward chain `cutEq ⇒ sternBrocotEq ⇒
    mobiusEq` is unconditional PURE.

## Companion specs

`seed/RESOLUTION_LIMIT_SPEC.md`,
`seed/THEOREM_METHODOLOGY_SUITE.md`,
`seed/META_SCAN_ARCHETYPES.md`,
`seed/CLOSED_FORM_SPEC.md`.  Per-conjecture catalogue at
`research-notes/G35_chiral_cup_ring_catalog.md`.
