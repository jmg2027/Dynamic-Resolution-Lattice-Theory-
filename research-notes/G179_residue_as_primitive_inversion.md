# G179 — the inversion: residue (self-pointing) as primitive, Raw as derived

**Date**: 2026-06-02.  **Status**: exploration / design note (direction (ii) from the
residue-form discussion).  **Companion**: `theory/essays/the_form_of_the_residue.md` (the
synthesis, direction (i)); `research-notes/G178`.

## The move

Direction (i) takes **Raw as primitive** and reads everything *out* of it (the form =
source-without-enclosure).  Direction (ii) inverts: take the **self-pointing act** (the
constructor functor `F(X) = {a} ⊎ {b} ⊎ {x/y : x ≠ y}`) as primitive, and **derive** Raw as
its initial algebra, with the residue's escape-face as the co-part.

## The central finding — (i) and (ii) are one formal content, read two ways

The inversion needs **no new Lean**.  It is the *same* two theorems read with `F` (the act)
as primitive instead of Raw:

  - **Raw is derived = Raw is the initial `F`-algebra (μF).**  `HasDistinguishing` IS the
    `F`-algebra structure (two points + a symmetric `combine`); `raw_initial` /
    `universalMorphism = Raw.fold` is exactly "Raw is the initial algebra of the self-pointing
    functor — every other realization receives a unique map from it."  So Raw is not posited
    as the ground; it is *the least realization of the act*.
  - **The residue is the νF co-part = the self-cover surplus.**  The canonical map from the
    finite (μF) into the predicate algebra, `Object1 : Raw → (Raw → Bool)`, is injective but
    **not** surjective (`object1_not_surjective`); the surplus is the part with no
    well-founded finite descent — the νF (greatest-fixed-point / coinductive) co-part the
    `Lambek` header already notes ("Lambek alone holds for νF too").

So `ResidueForm.no_exterior_source_without_enclosure` is *also* the inversion's statement:
read forward it says "Raw sources everything, encloses nothing"; read backward it says "the
act's initial algebra is Raw, its co-part is the residue."  Per `05_no_exterior` §5.4, which
of {Raw, the act} is "primitive" is itself a **Lens choice**, not a fact — neither is more
primitive; the dichotomy is the import.  That is why the inversion is free: it is a change of
reading, not of content.

## What the inversion makes vivid (and the µF/νF mirror)

  - **µF (Raw)** — the *convergent* face: `decompose` + well-founded `isPart_wf` +
    `terminal_iff_atom` (`Theory/Raw/Lambek`).  Every descent bottoms out at an atom; the
    initial algebra is finite trees.
  - **νF (residue)** — the *escaping* face: the non-well-founded co-part, witnessed (in
    Mathlib-free Lean, which has no native coinduction) by the **stream-coalgebra
    non-surjectivity**: Raw embeds into `Raw → Bool` (an `F`-coalgebra-like object of
    "infinite-support" readings) but does not exhaust it (`object1_not_surjective`,
    `cantor_raw_bool`).  The undifferentiated `fun _ => true` is the named νF inhabitant
    outside µF's image (`residue_witnessed`).

The two are the two fixed points of the one act; the canonical `µF → νF` is the self-cover,
injective-not-surjective — the residue is exactly `νF ∖ image(µF)`.

## The one genuinely-open piece — a native νF

What is *not* yet formal: a **native final `F`-coalgebra** (νF) object, with the canonical
`µF → νF` as a Lean map whose non-surjectivity recovers the residue intrinsically (rather
than via the `Raw → Bool` shadow).  Mathlib-free Lean 4 has no primitive coinduction, so this
needs either:

  - a fuel-bounded / stream approximation (`Nat → F`-layer; the re-entry stream `Nat → Raw`
    we already use in `descent_chain_drops` and the orbits) — the **tractable first step**:
    define the coalgebra of infinite peel-streams and show Raw = the well-founded sub-part,
    the residue = the non-terminating remainder; or
  - a `Quotient`/setoid coinductive emulation (encoding cost, like the canonical-form subtype
    emulates the slash quotient).

Honest scope: this would give the residue's escape-face a *positive native* form (a
coalgebra), complementing the *negative* form (non-image).  It does **not** capture the
residue as one object — the νF is still read by a coalgebra Lens; the residue stays outside
every view (the guard of `the_form_of_the_residue.md`).  And it must avoid the category error
of forcing one operator across `not` / peel / `Object1` (rejected throughout G172/G175/G177).

## Why the inversion matters for self-standing

Taking the act (F) as primitive sharpens "self-justified": the framework's ground is not an
*object* (Raw) that one might ask the provenance of, but the *act of distinguishing* whose
two fixed points (finite Raw, escaping residue) are co-derived.  "What sources the act?" has
no operand (§5.1) — the act is the asking.  This is the §5.6 reading (the Möbius iterator as
the self-reference loop's surrogate, converging to φ) taken as the starting point rather than
the destination.

## First step — DONE (`Theory/Raw/MuNuMirror`, 7 PURE)

The escape's **finite depth/tower shadow** is now closed (∅-axiom) — NOT a νF object (an
adversarial review corrected the first draft's "positive native νF form" overclaim; these
quantify over finite Raws):

  - `depth_cofinal` / `ascent_unbounded` — depths cofinal in ℕ; no *finite* Raw caps the
    upward self-pointing `rawTower` (`∀ N, ∃ r, N < r.depth`).  The finite shadow of the
    open νF (the Raw-floor analogue of the tower-scale `DepthCeilingResidue` "no top").
  - `tower_ascent_isPart` — the genuinely new bit: an *explicit total* upward `IsPart`-stream
    (`rawTower`, each rung peels from the next).
  - `ascent_total_descent_partial` — an existential (total ascending stream) vs a
    universal-negation (`no_infinite_descent`, imported from `Lambek`).  Honest: NOT two
    symmetric "faces of one operator" — the descent half is not new, the asymmetry is
    ∃-vs-¬∃.
  - `ascent_adds_unit` — one rung = the count-Lens unit `+1` (same unit the descent drops by,
    `part_depth_succ_le`).  `tower_no_cycle` — the ascent never returns.
  - `descent_wf_ascent_unbounded` — convenience bundle (no new content): `isPart_wf` ∧
    `ascent_unbounded` ∧ `terminal_iff_atom`.

Honest scope (review verdict): these are finite-Raw `∀∃`/`¬∃` *descriptions*, paired with the
negative `object1_not_surjective` — **not** a νF object, and no operator unifies the
directions.  The genuinely new theorem is `tower_ascent_isPart` (the explicit ascending
stream); the depth-unboundedness is `ℕ`-cofinality via `rawTower_depth`.

## Second step — the structural escape (route (a), DONE) (`Theory/Raw/CoResidue`, 8 PURE)

Beyond the depth shadow: a **structural** emulation of νF via the path-function model
`CoShape := List Bool → Bool` (a node at path `p` is a branch iff `s p = true`), with the
`F`-coalgebra readout `coOut` (`coIsBranch`/`coLeft`/`coRight`):

  - `allBranch := fun _ => true` — the **infinite complete self-pointing**: a branch at every
    path (`allBranch_no_leaf`), its own left subtree (`allBranch_coLeft_self`, pointwise, no
    `funext`) — genuine infinite `coOut`-descent (G180 spec item 4);
  - `toShape : Tree → CoShape` — the finite-Raw embedding; every finite tree has a leaf path
    (`tree_has_leaf_path`);
  - ★ `raw_ne_allBranch` — `toShapeRaw r ≠ allBranch` for every Raw: **no finite Raw is the
    infinite tree** (the escape, structurally, via a named inhabitant — G180 spec item 3);
  - `structural_escape` — the bundle (infinite descent + outside the image).

This is richer than the depth shadow (a named co-tree with genuine non-termination), and
∅-axiom (the `≠` is a pointwise difference, no `funext`).

## Third step — the anamorphism (the existence half of finality) (`CoResidue` §5)

A modest advance toward the universal property, ∅-axiom: the **anamorphism** `ana` unfolds
*any* `F`-coalgebra `c : X → Bool × X × X` into `CoShape`, commuting with the `coOut`
projections (`ana_isBranch`/`ana_coLeft`/`ana_coRight`, all `rfl`).  So every coalgebra admits
an unfold — the **existence** half of finality.  Both faces are unfolds: `toShape_eq_ana`
(finite embedding = unfold of the tree's coalgebra `treeCoalg`) and `allBranch_eq_ana`
(infinite inhabitant = unfold of the always-branch coalgebra).  `unfold_existence_and_escape`
bundles existence + both-faces + the escape (`raw_ne_allBranch`, from the structural step).

Honest (after adversarial review): only **existence** of unfolds (+ three `rfl`
commutations) is proven — *not* the object-property "weakly final" (the name was dropped) and
*not* uniqueness (full finality).  The `rfl` commutations are the computation rule of `ana`.
The escape conjunct is re-exported from the structural step, not new.

## Still open — uniqueness/injectivity (full Lean-native νF)

`CoResidue` remains an **emulation**: `CoShape` is the full function space (not the
well-formed cotree subtype), `toShape` is not injective (`Bool`-`CoShape` conflates the two
atoms — a faithful embedding needs a leaf-labelled `CoShape`), and the unfold's *uniqueness*
(finality proper, via bisimulation) is unproven.  A genuinely Lean-native νF — leaf-labelled
carrier + injective `toShape` + final-coalgebra uniqueness — remains open (Mathlib-free Lean
has no coinduction primitive; would need a setoid emulation with encoding cost).  The
existence half (route (a)+anamorphism) is the honest tractable realisation; uniqueness is the
deeper deferred piece.
