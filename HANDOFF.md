# Session handoff

Branch: `claude/unified-math-foundation-1QJHR`.  Built clean
(`cd lean && lake build`); `E213.Lens.Unified` scans **9 PURE / 0
DIRTY**.

## This session

Unified-equivalence synthesis: defined the 213-native concept that
subsumes equivalence, equivalence class, isomorphism, and
homomorphism (동치 / 동치류 / 동형 / 준동형) as the **Lens-arrow**
(= `Lens.refines L M`).

  · `theory/lens/unified_equivalence.md` — synthesis chapter.
    Single-concept thesis, four classical readings as
    decompositions, canonical-form ladder `cutEq ⇒ sternBrocotEq
    ⇒ mobiusEq` via Möbius P = [[2, 1], [1, 1]], Eqv ↔
    Lens.equiv collapse, axiom-cost table, what-this-is-not.
  · `lean/E213/Lens/Unified.lean` (9 PURE) — `LensIso`,
    `LensFiber`, `lensIso_refl / symm / trans`,
    `lensIso_iff_kernel_eq`, `LensFiber.self`, `fibers_complete`,
    `morphism_is_arrow`.
  · `theory/lens/INDEX.md` — synthesis-chapters section added;
    Unified.lean registered as Lean anchor.
  · `lean/E213/Lens.lean` — Unified import wired into the Lens
    spec-as-code umbrella.

## Boot order

  · `seed/AXIOM/05_no_exterior.md` §5, §8.4 — re-read every
    session start
  · `theory/lens/unified_equivalence.md` — the single-concept
    statement (start here for any equivalence / iso / hom
    question)
  · `theory/INDEX.md` — book map
  · `lean/E213/ARCHITECTURE.md` — layer ring spec
  · `theory/PROMOTION_CRITERIA.md` — Hard / Soft gates

## Where the unification lives

Quick anchors for the next session that needs to read or extend
the unification:

  · Strict ∅-axiom backbone: `lean/E213/Lens/Unified.lean` (9
    PURE) — the named theorems
  · Existing Lens-arrow infrastructure (PURE): `LensCore.lean`
    (Lens.equiv, Lens.refines), `Lens/Algebra/Congruence.lean`
    (slash-cong forward), `Lens/Compose/Morphism.lean`
    (IsLensMorphism → refines), `Lens/EqPW.lean` (pointwise
    Lens equality), `Lens/Congruence.lean` (Eqv ↔ Lens.equiv)
  · Reverse direction (sealed-DIRTY by `STRICT_ZERO_AXIOM.md`
    category (b)): `Lens/Algebra/Corresp.lean`
    (`kernel_correspondence`) via `Lens/Universal/QuotLens.lean`
    (`universalLens` + `universalLens_kernel_eq_E`)
  · Canonical algebraic form (PURE): `Lib/Math/Real213/
    Mobius213Equiv.lean` (P-orbit chains + mobiusEq +
    `mobiusEq_of_cutEq`) and `Mobius213SternBrocot.lean`
    (mediant closure + sternBrocotEq +
    `sternBrocotEq_of_cutEq`)

## What's closed (chapter level)

Highlights — full list in `theory/INDEX.md`:

  · `theory/lens/unified_equivalence.md` — 동치 / 동치류 / 동형 /
    준동형 single-concept synthesis (this session)
  · `theory/math/cohomology/k_nm_c_classification.md` —
    universal `(NS, NT, c)` cohomology framework (EnrichedKNSNTc)
    + codim ≥ c parametric + codim ≤ c dual-span (conditional +
    c = 1 unconditional + cross-layer unconditional) + arbitrary
    -m bilateral kill (`9·m` cancellation in `NatBeqHelpers`)
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
  · `theory/essays/c_counter_programme_closure.md` —
    cross-cutting synthesis of the c-counter five-direction
    closure + same-shape parallel to P-orbit

## What's open (residual)

Inherited from prior sessions; no new opens this session.

  · **Per-layer completeness (HARD direction)** for unconditional
    `codim = c`: joint ψ-kernel ⊆ `InPrimaryCupSpanPlusBoundary`.
    EASY direction closed unconditional at every c
    (`primary_cup_span_soundness_all_c`).  HARD reduces to
    single-layer K_{3,3} dim count (9-element face space modulo
    (im δ¹ + primary cup-image) has dim 1); needs 8 explicit
    InPrimary generators spanning the dim-8 ψ-kernel at c=1.
    Layer-disjointness then lifts to ∀c.
  · **Cochain-level mediant functor**: count-level Vandermonde
    closed; lifting to cup-product algebra (4 edge + 9 face
    sub-cells per mediant) is the next layer.
  · **Massey-class mediant lift**: do K_{4, 3} 4-fold Massey
    witnesses factor through K_{1, 1} ⊕ K_{3, 2}?
  · **Pell-orbit extensions**: (8, 5), (5, 4), (7, 4), (13, 8)
    — next Stern-Brocot layer.  Concrete reachable witnesses;
    structural cohomology transports via Direction A.
  · **n-prime P-orbit depth bound**: empirically D(p) ≤ 4 for
    p ≤ 97; asymptotic growth (O(log p)?) is open.
  · **Cup-product transport on V32LocalSignature**: does the
    (2, 1, 3) local signature persist under cup
    `H^k × H^l → H^(k+l)` at K_{3, 2}^{(c=2)}?
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
