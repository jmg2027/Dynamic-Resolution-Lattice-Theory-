# G180 — the escape at every scale: three finite shadows of one open νF

**Date**: 2026-06-02.  **Status**: synthesis (consolidates the residue-form escape face) +
the precise spec for the open νF (sets up the native-coalgebra track).
**Companions**: `theory/essays/the_form_of_the_residue.md`, `research-notes/{G178,G179}`.

## The thread

The residue's **escape** face — "naming/iterating the act leaves a surplus the act does not
reach" — is closed ∅-axiom at *three* scales.  Each is a **finite shadow**: a `∀∃` / `¬∃`
statement about finite objects, none of them a completed infinite object.  This note pins
that they are the *same* escape, and specs exactly what the (still open) native νF would be —
the one infinite object all three shadow.

## The three shadows (all closed, all ∅-axiom)

  - **Predicate scale** (`Lens/FlatOntologyClosure.object1_not_surjective`,
    `Cardinality.cantor_raw_bool`): the self-cover `Object1 : Raw → (Raw → Bool)` is faithful
    but not surjective — naming "everything pointable" leaves the Cantor surplus.  Negative
    form (a non-image).
  - **Raw-floor scale** (`Theory/Raw/MuNuMirror`): the act iterated *upward* — `rawTower`,
    depth `n` at rung `n` — has depths cofinal in `ℕ`; no finite Raw caps the ascent
    (`ascent_unbounded`, `∀ N, ∃ r, N < r.depth`), with an explicit total ascending
    `IsPart`-stream (`tower_ascent_isPart`) against the well-founded descent
    (`Lambek.no_infinite_descent`).  Depth/tower shadow.
  - **Tower-ceiling scale** (`Cauchy/{DepthCeilingResidue, DepthHeightDiagonal,
    DepthOverflowDuality}`): naming a whole family/height at once escapes it —
    `diag_not_in_seq` (`diag f ≠ f i` ∀i), `height_diagonal_escapes`, `overflow_escapes`
    (`overflow ⟹ val ∉ family`); `ceiling_residue_is_pointing_residue` already identifies the
    ceiling residue with the pointing residue (`self_covering_closure`).  Diagonal shadow.

## Why they are one escape

All three are the same structural fact — *the act, applied to all of its finite
realisations at once, exceeds every one of them* — read through three readouts:

| scale | the "all at once" act | the readout | the escape statement |
|---|---|---|---|
| predicate | point at every Raw (indicator algebra) | `Raw → Bool` | `Object1` not surjective |
| Raw-floor | iterate the slash upward (`rawTower`) | `depth : Raw → ℕ` | depths cofinal, no finite cap |
| tower-ceiling | name the whole family/height | `diag` / `overflow` | `diag f ≠ f i` ∀i |

`ceiling_residue_is_pointing_residue` already ties the predicate and tower scales; the
Raw-floor shadow (`MuNuMirror`) is the third, via `depth`.  The unit by which each escapes is
the count-Lens `1` (`overflow_is_unit_surplus`: `bound i + 1 ≤ val i`; `ascent_adds_unit`:
one rung `+1`; the diagonal's `diag f i = f i i + 1`).  One escape, three readouts, one unit.

These are **shadows, not the thing**: each quantifies over finite objects (every family
index, every finite Raw) — none constructs the completed infinite self-pointing.  Per the
standing guard (`the_form_of_the_residue.md`), the residue stays outside every view; these
are escape *descriptions*.

## The spec for the open νF (sets up the native-coalgebra track)

The one infinite object all three shadow is the **final `F`-coalgebra νF** of the
self-pointing functor `F(X) = {a} ⊎ {b} ⊎ {x/y : x ≠ y}` — the (possibly) infinite
self-pointing trees, of which Raw = µF (the finite ones) is the initial-algebra sub-part.
The canonical inhabitant is the **infinite complete self-pointing** (e.g. the all-branch
tree, the limit of `rawTower`): a fixed point of "peel a child" that never reaches an atom.

A native νF construction must give, ∅-axiom and Mathlib-free (no coinduction primitive):

  1. a carrier `νF` with a coalgebra `out : νF → F νF` (every co-tree decomposes);
  2. an embedding `Raw → νF` (the finite trees), injective;
  3. **non-surjective**, with a *named* infinite inhabitant outside the image (the all-branch
     tree) — recovering the escape *structurally*, not via `depth`/predicate shadows;
  4. that inhabitant has an *infinite* `out`-descent (no atom floor) — the positive νF
     content the µF `no_infinite_descent` denies for finite Raw.

Tractable route (a): the **path-function model** `CoShape := List Bool → Bool` (a node at
path `p` is a branch iff `s p = true`); `allBranch := fun _ => true` is the infinite complete
tree (no leaf path, its own left-subtree — infinite descent); the finite-Raw embedding
`toShape` has a leaf path on every Raw, so `toShape r ≠ allBranch` for all `r` — the
structural escape.  (`≠` from a pointwise difference needs no `funext`.)  Route (b): a setoid
coinductive emulation (encoding cost).

This is the next track (direction (ii)'s deep piece).  Doing the synthesis first — pinning
the three shadows and the precise νF spec — is what makes the native construction
well-targeted and keeps it from re-overclaiming: the native νF must *add* item 4 (a named
inhabitant with genuine infinite descent), or it is just another shadow.

## Anchors

`Lens/FlatOntologyClosure.object1_not_surjective`, `Lens/Cardinality.cantor_raw_bool`;
`Theory/Raw/MuNuMirror.{ascent_unbounded,tower_ascent_isPart,ascent_total_descent_partial,ascent_adds_unit}`,
`Theory/Raw/Lambek.no_infinite_descent`; `Cauchy/DepthCeilingResidue.{diag_not_in_seq,
ceiling_residue_is_pointing_residue}`, `Cauchy/DepthHeightDiagonal.height_diagonal_escapes`,
`Cauchy/DepthOverflowDuality.{overflow_escapes,overflow_is_unit_surplus}`.
