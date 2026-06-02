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

## Next step (if pursued)

A small ∅-axiom experiment: the peel-stream coalgebra `S = Nat → Raw` with `IsPart`-steps;
`Raw` (well-founded, `no_infinite_descent`) as the terminating sub-part; the non-terminating
streams as the residue's native escape-form.  This would be the first *positive* coalgebraic
witness of the νF face, paired with the existing negative `object1_not_surjective`.  Deferred
unless the inversion is taken up as a track.
