# DIRTY recovery patterns via the Lens-arrow

**Status**: Methodology chapter.  Companion to
`theory/lens/unified_equivalence.md` (the single-concept
synthesis).

## Overview

`STRICT_ZERO_AXIOM.md` records ≈ 56 DIRTY theorems whose Lean-core
axiom use (`propext` and / or `Quot.sound`) is sealed by
structural categories (a) Prop-as-distinguishing and (b) Lens
funext-by-design.  This chapter gives a **toolkit for rephrasing
DIRTY claims as PURE Lens-arrow statements** when the DIRTY
content is incidental rather than structural — when the question
"what is the kernel?" already answers what the function-level Eq
was trying to assert.

The Lens-arrow (`theory/lens/unified_equivalence.md`) provides the
PURE replacement vocabulary: equivalence, equivalence class,
isomorphism, homomorphism are all aspects of one concept that
never needs propext or funext at the kernel level.

Each pattern below names:

  · the DIRTY shape (typical symptom)
  · the PURE Lens-arrow shape it converts to
  · the bridge lemma in `lean/E213/Lens/Unified.lean`
  · when the pattern does NOT apply (structural DIRTY)

## Pattern P1 — Lens-Eq → LensIso

### Symptom
A claim of the form `L = M : Lens α` (Cat-1 per
`STRICT_ZERO_AXIOM.md`).  The combine field is function-valued
or Prop-valued; `L = M` requires `funext` (Quot.sound) on
combine, and possibly `propext` if α = Prop.

### PURE shape
`LensIso L M`, equivalently `∀ x y : Raw, L.equiv x y ↔
M.equiv x y`.  The kernel-level statement carries the same
operational content for any downstream consumer who only uses
`L.view r` modulo Raw — which is the typical use.

### Bridge
`lensIso_of_eqPW` (`Lens/Unified.lean`).  Composition:

```
eqPW proof (PURE, available via Lens/EqPW.lean)
   │
   ▼  lensIso_of_eqPW
LensIso L M (PURE, the unification claim)
```

The combine-sym hypothesis `hLsym` is required because Lens
view-equality on `slash` reduces via `Raw.fold_slash`, which
itself needs symmetric combine.

### Does NOT apply when
The downstream consumer literally needs the function-level `L = M`
for definitional unfolding (e.g. a tactic rewriting on a term
shaped `L.combine`).  Those cases are sealed-DIRTY by design and
the `eqPW` companion + LensIso bridge cannot replace them.

## Pattern P2 — Mutual morphism pair → LensIso

### Symptom
A claim "L and M are isomorphic as Lens-algebras" stated via a
function-equality between `L.view` and `M.view ∘ h` and its
inverse — which usually goes through `funext` to compose to
identity.

### PURE shape
`LensIso L M` produced by exhibiting forward and backward
`IsLensMorphism` witnesses.

### Bridge
`lensIso_of_morphism_pair` (`Lens/Unified.lean`).  The morphism
predicate `IsLensMorphism h L M`
(`Lens/Compose/Morphism.lean`) is itself PURE; the bridge to
`refines` uses `refines_of_morphism` (also PURE under symmetric
combines).

### Does NOT apply when
The downstream consumer needs `h ∘ k = id` propositionally
(function equality).  At kernel level, `h ∘ k = id` becomes
"the composite morphism induces the identity refinement-arrow",
which `LensIso` already carries via the bidirectional
`Lens.refines`.

## Pattern P3 — Classical quotient → LensImage

### Symptom
Use of `Quot L.equiv` or `α / ~` as a quotient type.  Loads
`Quot.sound` whenever quotient elements are compared.

### PURE shape
`LensImage L`, the Σ-type
`{ a : α // ∃ r : Raw, L.view r = a }`.  Each element packages
a value plus a representative.  Equality of `(LensImage.proj L
x).val` and `(LensImage.proj L y).val` is **definitionally**
`L.equiv x y` — no `Quot.sound` invoked.

### Bridge
`LensImage`, `LensImage.proj`, `LensImage.proj_val_eq_iff`
(`Lens/Unified.lean`).  The `Iff.rfl` proof of
`proj_val_eq_iff` records that the Σ-type representation makes
kernel-equality definitional.

### Does NOT apply when
The downstream consumer specifically wants the quotient type's
`Quot.lift`-induced universal property — e.g., the unique
function out of `Quot L.equiv` that descends from a Raw → β
respecting L.equiv.  At Σ-type level, "the function descends"
becomes "the function only depends on L.view", which is the
same content but stated upstream.  The Σ-type version is
strictly stronger (no propositional collapse needed); rephrasing
the consumer to use it is a separate refactor.

## Pattern P4 — Slash-cong assertion → kernel inheritance

### Symptom
A claim "E is a slash-congruence" proven by exhibiting a Lens L
such that `L.equiv = E` (where the RHS is a function-equality
at type `Raw → Raw → Prop`, requiring propext + funext).

### PURE shape
Replace the existence claim by the forward implication only:
"E is a slash-congruence" follows from L being a Lens with
`L.equiv ⊆ E` pointwise (PURE via
`Lens.equiv_slash_congruence`).  Bidirectional kernel equality
goes through `universalLens` and is sealed-DIRTY.

### Bridge
`Lens/Algebra/Congruence.lean#Lens.equiv_slash_congruence`
(PURE, forward direction); `Lens/Algebra/Corresp.lean#
kernel_correspondence` for the bidirectional statement (DIRTY,
sealed by category (b)).

### Does NOT apply when
The consumer needs the full bijection `{Lens kernels} =
{slash-congruences}`.  Then `universalLens E` is the realising
Lens and the sealed-DIRTY direction is unavoidable — this is
the **structural DIRTY** case, not a pattern instance.

## Decision flow

```
Have a DIRTY claim → ask:

  · Does the claim assert `L = M : Lens α`?       → try P1
  · Does it claim an iso via mutual functions?    → try P2
  · Does it construct `Quot L.equiv`?             → try P3
  · Does it claim "E is the kernel of a Lens"?    → try P4
  · None of the above?                            → likely structural
                                                    DIRTY (category
                                                    (a) or (b));
                                                    seal it
```

## When to seal instead of recover

Categories (a) and (b) of `STRICT_ZERO_AXIOM.md` exist because
some uses of propext / funext are **the content**, not the
ergonomics.  The sealed list is documented; do not attempt to
recover those.  Specifically:

  · `Prop` as a `HasDistinguishing` instance (category (a)) —
    `combine_sym` on Prop IS the propext use.  Removing it
    removes the thesis "Prop is an atom of meaning".
  · `universalLens` constructions (category (b)) — the codomain
    `Raw → Prop` makes `combine_sym` a function-equality at
    Prop.  Removing it removes the kernel-realisation direction
    of `kernel_correspondence`.

Patterns P1–P4 apply to DIRTY claims that **incidentally**
inherited the seal (e.g. via a downstream `=` on a Lens that
the consumer only used at kernel level).  Recovery is then
clean: state the claim at LensIso / LensImage level, prove via
the bridge.

## Worked example

A Cat-1 candidate in pre-EqPW history was the function-Eq
between `idLens` and a Lens whose combine reproduces the same
view-function on Raw.  Two forms:

```
-- DIRTY: L_alt = idLens : Lens (Raw → Raw)
-- needs funext on combine
theorem L_alt_eq_idLens : L_alt = idLens := by funext _ _; rfl
```

vs.

```
-- PURE: kernels coincide on every Raw-pair
theorem L_alt_kernel_eq_idLens : LensIso L_alt idLens :=
  lensIso_of_eqPW
    ⟨rfl, rfl, fun _ _ => rfl⟩  -- the eqPW proof
    L_alt.combine_sym             -- symmetric combine hypothesis
```

The PURE form delivers the same operational content for any
downstream caller that uses the Lens via `view` / `equiv` /
`refines`.  Cat-1 conversions during the marathon (Phase 2 in
`STRICT_ZERO_AXIOM.md`) replaced ≈ 11 DIRTY theorems with the
eqPW companion; LensIso extends the same template to Lenses
of differing codomain α, β.

## Inductive-predicate level generalisation

P1 (Lens-Eq → LensIso via eqPW) is the **Lens-level** instance of
a more general principle: pointwise equality as the bridge that
replaces `funext`.  The same principle lifts to **arbitrary
inductive predicates on function-typed arguments**.

Concrete instance: `InPrimaryCupSpanPlusBoundary c`
(`lean/E213/Lib/Math/Cohomology/Bipartite/V33EnrichedParametricDualSpan.lean`)
is an inductive Prop on `EnrichedFaceVal c = Fin 3 → Fin 3 → Fin
c → Bool`.  Closing the HARD direction
`joint ψ-kernel ⊆ InPrimary` requires bridging from a candidate
function `⊕ᵢ bᵢ · gᵢ` (built from primary cup-products) to the
target `v`, which are pointwise-equal but not function-literal
equal.  Solution: extend the inductive with a `cong` constructor

```
| cong (v w : EnrichedFaceVal c) (h : ∀ s t m, v s t m = w s t m) :
    InPrimaryCupSpanPlusBoundary c w → InPrimaryCupSpanPlusBoundary c v
```

— pointwise equality propagates the inductive witness *through the
type itself*, not through an external axiom or external bridge
lemma.

This pattern is the **5th funext-avoidance pattern** documented in
`theory/essays/pure_funext_avoidance.md` (which complements this
chapter at the Padic / Real213 layer).  P1 and the cong
constructor share a single principle (pointwise-equality bridge);
they differ only in level — P1 brings two **Lens** values to
LensIso level; the cong constructor brings two **face cochains**
(or any function-typed inductive argument) to the same membership
class.

## Connection

  · `theory/lens/unified_equivalence.md` — the single-concept
    backbone these patterns rely on
  · `theory/essays/pure_funext_avoidance.md` — sister methodology
    chapter at Padic / Real213 / Cohomology layer; the 5th pattern
    (Inductive cong constructor) ↔ P1 at inductive-predicate level
  · `theory/essays/per_layer_completeness_constructive_closure.md`
    — concrete deployment of the cong-constructor pattern in the
    HARD direction of `codim ≤ c`
  · `STRICT_ZERO_AXIOM.md` — DIRTY catalog + sealed-by-design
    categories (a, b)
  · `lean/E213/Lens/EqPW.lean` — the Cat-1 funext-avoidance
    infrastructure
  · `lean/E213/Lens/Unified.lean` — PURE bridges
    (`lensIso_of_eqPW`, `lensIso_of_morphism_pair`,
    `LensImage` + `LensImage.proj_val_eq_iff`)
  · `lean/E213/Lens/Algebra/Congruence.lean` — P4 forward
    direction (PURE)
  · `lean/E213/Lens/Universal/QuotLens.lean` — P4 reverse
    direction (sealed-DIRTY, category (b))
  · `lean/E213/Lib/Math/Cohomology/Bipartite/V33EnrichedParametricDualSpan.lean`
    — cong constructor instance; see the `cong` case in
    `primary_cup_span_soundness_conditional`
