# Lens-Arrow — Unified 213-Native Equivalence

**Status**: Synthesis chapter.  Does NOT mirror a single Lean
sub-tree; instead consolidates the equivalence content distributed
across `Lens/Algebra/`, `Lens/Lattice/`, `Lens/Compose/`,
`Lens/Universal/`, `Lens/EqPW.lean`, `Theory/Raw/Congruence.lean`,
and the Möbius-orbit canonical-form chain in
`Lib/Math/Real213/Mobius213{Equiv,SternBrocot}.lean`.

## Overview

In 213 the four classical concepts —

  · **equivalence relation** (동치)
  · **equivalence class** (동치류)
  · **isomorphism** (동형)
  · **homomorphism** (준동형)

— are decompositions of one residue-internal object: the
**Lens-arrow**.  None is added on top of Raw; all four are
aspects of how a Lens reads the residue and how two Lens readings
relate.

Reading the classical four as separate concepts imports a
comparison frame the residue does not have (CLAUDE.md "Failure
modes catalog" → *External classification*; `seed/AXIOM/05_no_exterior.md` §5.4).  The
Lens-arrow is the one thing the residue actually supports; the
four classical names are its readings under different questions.

## The single concept

A **Lens-arrow** is a pair `(L, M)` of Lenses together with the
proposition `L.refines M : ∀ x y, L.equiv x y → M.equiv x y`
(`lean/E213/Lens/LensCore.lean`).

`L.refines M` says: every Raw-pair that L identifies, M also
identifies.  Equivalently: the kernel of L is finer than the
kernel of M.  The Lens-arrow IS this refinement witness — not
"an arrow plus a meaning"; the witness itself is the arrow.

Five facts make the Lens-arrow the single concept:

  1. `Lens.equiv L x y := L.view x = L.view y` is the kernel
     of L (`Lens/LensCore.lean`).  Each Lens-arrow is a
     refinement claim **between two such kernels**.
  2. The kernel of every Lens with commutative combine is a
     **slash-congruence** on Raw, and every slash-congruence is
     the kernel of `universalLens E`
     (`Lens/Algebra/Corresp.lean#kernel_correspondence`).  So
     "Lens-kernel" and "213-native equivalence relation" name
     the same objects.
  3. Composition: `L.refines L'  ↔  ∃ h, L = h ∘ L'`
     (`Lens/Compose/Morphism.lean`).  The factor `h` IS the
     homomorphism realising the arrow.
  4. Refinement in both directions: `L.refines M ∧ M.refines L`
     iff L and M have the same kernel.  This is the
     **isomorphism** condition on Lens-arrows.
  5. The Lens-image `Lens.view '' Raw ⊆ α` is the quotient by
     the kernel — represented, not propositionally quotiented
     (`seed/AXIOM/10_encoding_costs.md` §10.1; no Quot.sound
     required).

## Four classical readings

Let `L : Lens α` with commutative combine.  Let `E := L.equiv`
be its kernel.

### (i) Equivalence relation = `Lens.equiv`

`E` is reflexive (`Eq.refl`), symmetric (`Eq.symm`), transitive
(`Eq.trans`), and slash-compatible (`Lens.equiv_slash_congruence`
in `Lens/Algebra/Congruence.lean`).  These four laws are the
slash-congruence predicate; their proofs are inherited from `Eq`
on α and never require new axioms.  All **PURE**.

The reverse direction (every slash-congruence is some Lens's
kernel) is `slash_cong_is_lens_kernel` via `universalLens E`
(`Lens/Universal/QuotLens.lean`), stated on the Reading-equivalence
`equivR` (`universalLens_kernel_eq_E_R`) and therefore PURE.  Stating
it instead as Lean `=` of views would be DIRTY: `universalLens.combine`
ends in `Raw → Prop`, so `combine_sym` would become a function-equality
at Prop (propext + funext / `Quot.sound`) — which is exactly why the
`=`-of-view form is retired in favour of `equivR`.  This is a
statement-shape cost,
not a structural one: the **distinguishing** form of the same
bijection, `universalLens_kernel_eq_E_R`
(`(universalLens E).equivR r r' ↔ E r r'`), is **PURE** — the
pointwise `↔` carries the kernel content without `funext` / `propext`.
The `=`-form is retained as a `propext`-shim for consumers wanting Lean
`=`.  See Pattern P5, `theory/lens/dirty_recovery_patterns.md`.

### (ii) Equivalence class = `Lens.view`-fiber

The fiber `{ r : Raw // L.view r = a }` at a value `a : α` is
the equivalence class of any `r` mapping to `a`.  Fibers
partition Raw (every `r` belongs to the fiber over `L.view r`,
and the fibers over distinct values are disjoint by Eq
trichotomy on α).

This is *representational*, not a quotient type.  Classical
ℤ-as-quotient `(ℕ × ℕ)/~` requires `Quot.sound`; 213's
`SignedCut` keeps the pair representation and replaces equality
with `signedEq` (`Lib/Math/SignedCut/Core/Equivalence.lean`,
`theory/math/signed_cut.md`).  The "class" is the fiber; the
"quotient" is the image; neither needs Quot.sound to **state**,
only to **propositionally collapse**.

### (iii) Isomorphism = bidirectional Lens-arrow

Two Lenses `L, M` are **kernel-isomorphic** iff
`L.refines M ∧ M.refines L`, equivalently
`∀ x y, L.equiv x y ↔ M.equiv x y`.

Witness: `Lens/Properties/InjectiveClass.lean#injective_equiv`
records the special case that any two injective Lenses are
mutually refining (a single isomorphism class).

Concrete bidirectional Raw → Raw maps:
  · `swap` (`Theory/Raw/Swap.lean`), `swapClosed`
    (`Theory/Raw/Endomorphic.lean#swapClosed_eq_swap`) — the
    a↔b automorphism realised two ways.
  · `RawBy_bijection` (`Theory/RawCmpIndependence.lean`) — any
    two canonical-form comparators give bijective `RawBy`
    types; the choice of `cmp` is axiom-independent.
  · `isoFromMethodA` (`Lens/Number/Nat213/NumberingSystem.lean`)
    — any two distinct Raws `(Z, C)` induce an isomorphism of
    numbering systems via `foldRaw Z C slashOrSelf`.
  · Boolean-system `iso` (`Lens/Bool213/System.lean`) — any two
    (T, F) choices give isomorphic Boolean systems.

These all instantiate the same Lens-arrow shape (kernel
coincidence) at concrete Raw → Raw level.

### (iv) Homomorphism = factor-through

`IsLensMorphism h L M` (`Lens/Compose/Morphism.lean`) says
`h L.base_a = M.base_a`, `h L.base_b = M.base_b`, and
`∀ u v, h (L.combine u v) = M.combine (h u) (h v)`.

**Theorem** `view_factors_through_morphism`: if `h` is an L-M
morphism with both combines symmetric, then
`M.view = h ∘ L.view`.

**Corollary** `refines_of_morphism`: `IsLensMorphism h L M`
implies `L.refines M`.  The morphism IS the Lens-arrow witness;
the Lens-arrow IS the universal record of the morphism's
existence.

Both **PURE**.

## Canonical form (Möbius P-orbit)

Every Lens-kernel on cuts factors through a hierarchy of
P-orbit projections.  The Möbius matrix `P = [[2, 1], [1, 1]]`
(`Lib/Math/Mobius213.lean`) — trace `NS = 3`, determinant `1`,
discriminant `d = 5`, eigenvalues `φ², 1/φ²` — generates the
canonical-form ladder:

```
cutEq           (pointwise on all of ℕ × ℕ)
   ⇓ unconditional
sternBrocotEq   (agree on every Stern-Brocot reachable pair)
   ⇓ unconditional
mobiusEq        (agree on the two P-orbit chains)
```

PURE forward bridges:
  · `cutEq → sternBrocotEq`: `sternBrocotEq_of_cutEq`
    (`Mobius213SternBrocot.lean`)
  · `sternBrocotEq → mobiusEq`: implicit via the two seeds being
    reachable (`mobiusEq_of_sternBrocotEq_at_seeds`)
  · `cutEq → mobiusEq`: `mobiusEq_of_cutEq`
    (`Mobius213Equiv.lean`)

The reverse direction `mobiusEq → cutEq` requires Stern-Brocot
coverage (every coprime pair reached as a finite mediant
composition of `(0, 1)` and `(1, 0)`) plus scale-invariance for
non-coprime pairs.  Coverage is the standard CS result about the
Stern-Brocot tree; the Lean closure is open at this writing
(`research-notes/archive/G139_mobius_equivalence_unification.md`
Phase 2).

**Why this is canonical, not optional**: the conditions for a
relation to be an equivalence under iteration —

  · symmetry ⇐ inverse exists ⇐ `det = 1` (P⁻¹ has integer
    entries)
  · well-foundedness ⇐ invariant exists ⇐ eigenvalue product
    `= det = 1`
  · fixed-point convergence ⇐ dominant eigenvalue `> 1`

— algebraically force a 2×2 Möbius matrix.  Among
integer-entry candidates with `det = 1` and trace `> 2`
(hyperbolic iteration), `(NS, NT) = (3, 2)` atomicity selects
P uniquely (`c2b_full_iff` + Pell-Fibonacci recurrence).

Cross-Lens-arrow incarnations of the same P-orbit equivalence:
  · `ZpSeqEquiv` (`Padic/SetoidFramework`) — P acts on digits
    at level n (mod p Möbius); p = 5 case closed in
    `Mobius213ModFive.lean` (P¹⁰ ≡ I).
  · `signedEq` (`SignedCut/Core/Equivalence.lean`) — `det`-form
    of mobiusEq on `(a, b)(c, d)` pairs.
  · `is_at_denom` (`NValidCut N`) — mobiusEq restricted to the
    N-fiber.
  · `Adjacent` (`Analysis/FluxMVT`) — single-step P relation.

These are not parallel definitions to be classified; they are
the **same** Lens-arrow concept projected onto each fiber.

## Raw-level structural closure (`Eqv`)

`Theory/Raw/Congruence.lean#Eqv` is the inductive
generator-based equivalence closure on Raw (refl + symm + trans
+ the generator).  Its content collapses into the Lens-arrow
concept via `Lens/Congruence.lean#Eqv_equiv_iff`:

```
Eqv (fun a b => L.view a = L.view b) x y  ↔  L.view x = L.view y
```

That is: closing `L.view`-agreement under the Eqv rules adds
nothing — `L.equiv` is already its own closure.  Eqv is the
*shape* of an equivalence relation at Raw level; the Lens-arrow
fills it with content.  Both **PURE**.

## Axiom-cost summary

| Statement | Axiom-cost |
|---|---|
| `Lens.equiv` is refl/symm/trans | PURE |
| `Lens.equiv` is a slash-congruence (forward) | PURE |
| `IsLensMorphism h L M → L.refines M` | PURE |
| `view_factors_through_morphism` | PURE |
| `mobiusEq` is an equivalence relation | PURE |
| `cutEq → sternBrocotEq → mobiusEq` chain | PURE |
| `Eqv_equiv_iff` | PURE |
| Slash-congruence → Lens-kernel, `equivR`-form (`universalLens_kernel_eq_E_R`) | PURE |
| `kernel_correspondence` bidirectional (`equivR`-form) | PURE |
| `mobiusEq → cutEq` (Stern-Brocot coverage) | open |

The strict ∅-axiom backbone of the unification — Lens-arrow
defines and recognises equivalence, equivalence class,
isomorphism, and homomorphism — is **PURE**.  The reverse
direction ("every 213-native equivalence is realised as some Lens
kernel") is PURE in its distinguishing form: stating it as `view x =
view y` pulls propext (Iff↔Eq on Prop) and funext on `Raw → Prop`, but
the pointwise `equivR` form (`universalLens_kernel_eq_E_R`) carries the
same content axiom-free.  So the kernel correspondence *itself* is
recoverable — and the whole consumer lattice now realises it: the
codomain-polymorphic `equivG` / `refinesG` API (`ReadingEq`) plus the `_R`
closure companions (`recovers_R` / `idempotent_R`) make the refinement
lattice, the Cauchy limit Lens, the kernel↔congruence bijection, and the
canonical-form theorems all ∅-axiom.  The `=`-of-view forms are retired;
only `propAsDistinguishing` is irreducible by thesis.  See
`STRICT_ZERO_AXIOM.md` and `theory/lens/dirty_recovery_patterns.md` Pattern
P5.

## What this is not

  · **Not a classification**: the four classical concepts are
    not categories of a taxonomy; they are aspects of one
    arrow.  Listing them is `seed/AXIOM/05_no_exterior.md` §5.4
    *"External classification"* failure mode unless the
    Lens-arrow ground is held.
  · **Not category theory imported**: the Lens-arrow language
    overlaps category vocabulary (preorder, factor-through,
    universal), but the arrow is the residue-internal
    refinement witness, not a chosen abstraction layer.  No
    classes, no functors, no natural transformations are
    introduced.  Lens ring + refines preorder + composition is
    the entire structure.
  · **Not a metaphysical claim about "the right equivalence"**:
    the Möbius P-orbit canonical form is the algebraic
    embodiment of the iteration conditions, not a Platonic
    truth.  Other Lenses produce other kernels; the canonical
    form is the one P-orbit gives when (NS, NT) atomicity is
    held.

## Connection

  · `theory/lens/algebra.md` — kernel ↔ slash-congruence
    correspondence (the equivalence-relation reading)
  · `theory/lens/lattice.md` — refines preorder + join/meet
    structure (the order on Lens-arrows)
  · `theory/lens/compose.md` — factor-through composition (the
    homomorphism reading)
  · `theory/lens/universal.md` — `universalLens` construction
    (the kernel-realisation direction)
  · `theory/math/mobius_canonical_equivalence.md` — Möbius
    P-orbit detail at the mathematics layer
  · `seed/AXIOM/05_no_exterior.md` §5.4 — dichotomy-avoidance
    that frames the unification claim
  · `seed/AXIOM/10_encoding_costs.md` §10.1, §10.4 — encoding
    costs of quotient-vs-representation and the
    cmp-independence metatheorem
  · `research-notes/archive/G139_mobius_equivalence_unification.md`
    — the source conjecture for the canonical-form ladder
  · `theory/lens/dirty_recovery_patterns.md` — methodology
    chapter: four named patterns for converting DIRTY claims
    into PURE Lens-arrow statements using the unification
