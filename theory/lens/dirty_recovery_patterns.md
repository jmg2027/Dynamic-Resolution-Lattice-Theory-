# DIRTY recovery patterns via the Lens-arrow

**Status**: Methodology chapter.  Companion to
`theory/lens/unified_equivalence.md` (the single-concept
synthesis).

## Overview

`STRICT_ZERO_AXIOM.md` records ≈ 56 DIRTY theorems whose Lean-core
axiom use (`propext` and / or `Quot.sound`) traces to two sources:
(a) `Prop` as a distinguishing atom, and (b) Lens kernel / refinement
claims stated as function-`=` of views.  This chapter gives a
**toolkit for rephrasing DIRTY claims as PURE Lens-arrow statements**:
the question "what is the kernel?" already answers what the
function-level Eq was trying to assert.

Of the two sources, only (a) is a genuine thesis-cost.  Source (b) is
a **statement-shape** cost — function-`=` of `Prop`-valued views pulls
`funext` (= `Quot.sound`) and `propext`, but the distinguishing
content it carries is the pointwise `↔`, which is PURE (Pattern P5).
The load-bearing kernel hub on the universal Lens family has a PURE
Reading-native form (`universalLens_kernel_eq_E_R`), and the whole
refinement lattice on Prop-valued Lenses is now **stated on the
codomain-polymorphic `equivG` / `refinesG` API** (PURE).  The `=`-of-view
forms are retired, not sealed.

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
A consumer literally needs the bijection `{Lens kernels} =
{slash-congruences}` stated as Lean `=` of view-functions.  That form
would require funext/propext — which is exactly why it is retired: the
Reading-native bijection `kernel_correspondence` /
`universalLens_kernel_eq_E_R` (`equivR r r' ↔ E r r'`) carries the same
content PURE (see Pattern P5), and is the form the codebase uses.

## Pattern P5 — Lens-`equiv` at a Prop codomain → `equivR` / `refinesR`

### Symptom
A kernel / `refines` / `combine_sym` / `view_eq` claim about a
`Prop`-valued Lens (`Lens (Raw → Prop)` — the universal / indexed /
Cauchy family) that bottoms out in
`Lens.equiv L x y := (L.view x = L.view y)`.  Because `view x : Raw →
Prop`, that `=` is a **function-of-`Prop` equality**, so it pulls
`funext` (= `Quot.sound`) and `propext` — independent of how clean the
surrounding proof is.  This is the single root of the whole
funext / propext seal set on Prop-valued Lenses: every sealed
`combine_sym` / `view_eq` / kernel / `refines` theorem in that family
inherits the cost from this one definition.

### PURE shape
The 213-native notion of "the same under `L`" is the
**distinguishing-equivalence** — `L` separates `x` and `y` the same
way — stated pointwise as `↔` rather than as `=` of the view-functions:

```
Lens.equivR  L x y := ∀ s, L.view x s ↔ L.view y s
Lens.refinesR L M  := ∀ x y, L.equivR x y → M.equivR x y
```

`equivR` carries the full equivalence-relation structure
(`equivR_refl` / `equivR_symm` / `equivR_trans`) and `refinesR` its
reflexive-transitive order — all PURE.  Using `=` instead imports
`Prop` / function identity beyond the distinguishing content, the
"View promoted to identity" slip (CLAUDE.md failure catalog;
`seed/AXIOM/06_lens_readings.md` §6.3, which mandates staying in the
decidable / distinguishing layer out of `=`-at-`Prop`).

### Bridge
`Lens/ReadingEquiv.lean` carries the `equivR` / `refinesR` structure
(PURE).  The kernel hub `universalLens_kernel_eq_E_R`
(`Lens/Universal/QuotLens.lean`) — `(universalLens E).equivR r r' ↔ E
r r'` — is the load-bearing Reading-native kernel, **PURE** (built from
`universalLens_view_eq_pw` + `Iff.trans`, ultimately
`Raw.fold_slash_iff`).  Composition:

```
Raw.fold_slash_iff (Theory, PURE — pointwise ↔ fold/slash homomorphism)
   │
   ▼  universalLens_view_eq_pw / universalLens_combine_sym_pw
universalLens_kernel_eq_E_R  (PURE kernel hub)
```

A one-direction shim back to the `=`-world,
`equivR_to_equiv` (`funext s; propext (h s)`), is retained and is the
**lone** `propext` / `Quot.sound` cost — for any consumer that
genuinely wants Lean `=`.

### Scope — full rebuild done, surface retired
The `universalLens` (`Raw → Prop`) kernel hub is recoverable PURE
(`combine_sym_pw`, `view_eq_pw`, `kernel_eq_E_R`), and the whole consumer
lattice is now **rebuilt onto the pointwise API** — the three walls a first
attempt hit are each resolved:

  1. **API restated pointwise, codomain-polymorphically.**  `ReadingEq α`
     (per-codomain reading-sameness: `=` at the default instance, pointwise
     `↔` at `Raw → Prop`) lifts `equivR` to `Lens.equivG` / `Lens.refinesG`,
     which reduce *definitionally* to `equiv` and `equivR`.  Consumers no
     longer inherit a `=`-cost.
  2. **Codomain-polymorphism replaces the per-codomain gap.**  `equivG` /
     `refinesG` type at any codomain; the source lenses being joined keep
     their own sameness while the `Raw → Prop` join targets read via `equivR`.
     (The dependent-product meets `iProdLens` were already PURE pointwise.)
  3. **Closure companions materialized.**  `universalLens_recovers_R` /
     `universalLens_idempotent_R` are PURE, via the new
     `universalLens_equivR_slash_congruence` (the `equivR` slash-congruence,
     from the generic `equivG_slash_congruence` + `combine_cong_pw` /
     `fold_pw`).

So P5 recovers the hub, and the rebuild carries it the rest of the way: the
`=`-of-view forms (`combine_sym`, `view_eq`, `kernel_eq_E`, `recovers`,
`idempotent`) are **deleted**, every consumer (`Lattice.*`, `Cauchy`,
`Corresp`, `Choice`, `CanonicalForm`) is ∅-axiom, and the lone `=`-cost is the
isolated `equivR_to_equiv` bridge.

### Does NOT apply when
`propAsDistinguishing` — `Prop` itself as a `HasDistinguishing`
instance — is the codomain *content*, not the kernel statement shape.
That seal is `propext` expressing the thesis "Prop is an atom of
meaning"; `equivR` does not touch it (see "When to seal" below).

## Decision flow

```
Have a DIRTY claim → ask:

  · Does the claim assert `L = M : Lens α`?       → try P1
  · Does it claim an iso via mutual functions?    → try P2
  · Does it construct `Quot L.equiv`?             → try P3
  · Does it claim "E is the kernel of a Lens"?    → try P4
  · Is it a kernel / refines / combine_sym on a
    Prop-valued Lens, bottoming out in
    `view x = view y`?                            → try P5
  · None of the above?                            → likely structural
                                                    DIRTY (category
                                                    (a)); seal it
```

## When to seal instead of recover

Exactly one source is genuinely **the content**, not the ergonomics:

  · `Prop` as a `HasDistinguishing` instance (`propAsDistinguishing`,
    category (a)) — `combine_sym` on Prop IS the propext use.
    Removing it removes the thesis "Prop is an atom of meaning".
    This is a handful of theorems and stays sealed.

Source (b) — `universalLens` and the wider Prop-valued Lens family — is
**fully recovered**: kernel hub + combine/view coherence by Pattern P5
(`kernel_eq_E_R`), the closure theorems by the `_R` companions
(`universalLens_recovers_R` / `universalLens_idempotent_R`), and the
`=`-based consumer surface by the codomain-polymorphic `equivG` / `refinesG`
API (the non-`Prop`-codomain gap closed by `ReadingEq`).  The `=`-of-view
forms are deleted; only `propAsDistinguishing` is irreducible by thesis.

Patterns P1–P5 apply to DIRTY claims that inherited the seal from a
statement shape (a downstream `=` the consumer only used at kernel
level; a function-`=` of Prop-valued views) and whose codomain admits
the pointwise form.  Recovery is then clean: state the claim at
LensIso / LensImage / `equivR` level and prove via the bridge.

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
`refines`.  The Cat-1 conversions catalogued in
`STRICT_ZERO_AXIOM.md` replaced ≈ 11 DIRTY theorems with the
eqPW companion; LensIso extends the same template to Lenses
of differing codomain α, β.

## Inductive-predicate level generalisation

P1 (Lens-Eq → LensIso via eqPW) is the **Lens-level** instance of
a more general principle: pointwise equality as the bridge that
replaces `funext`.  The same principle lifts to **arbitrary
inductive predicates on function-typed arguments**.

Concrete instance: an inductive Prop on a function-typed argument
(e.g. `EnrichedFaceVal c = Fin 3 → Fin 3 → Fin c → Bool`) where
closing a membership claim requires bridging from a candidate
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
`theory/essays/methodology/pure_funext_avoidance.md` (which complements this
chapter at the Padic / Real213 layer).  P1 and the cong
constructor share a single principle (pointwise-equality bridge);
they differ only in level — P1 brings two **Lens** values to
LensIso level; the cong constructor brings two **face cochains**
(or any function-typed inductive argument) to the same membership
class.

## Connection

  · `theory/lens/unified_equivalence.md` — the single-concept
    backbone these patterns rely on
  · `theory/essays/methodology/pure_funext_avoidance.md` — sister methodology
    chapter at Padic / Real213 / Cohomology layer; the 5th pattern
    (Inductive cong constructor) ↔ P1 at inductive-predicate level
  · `theory/essays/cohomology/per_layer_completeness_constructive_closure.md`
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
  · `lean/E213/Lens/ReadingEquiv.lean` — P5 `equivR` / `refinesR`
    structure (PURE; lone shim `equivR_to_equiv`)
  · `lean/E213/Lens/Universal/QuotLens.lean` — P4/P5 reverse
    direction: `universalLens_kernel_eq_E_R` (`equivR`-form, PURE), the
    closure companions `recovers_R` / `idempotent_R`, and the `*_pw`
    combine/view/fold companions
