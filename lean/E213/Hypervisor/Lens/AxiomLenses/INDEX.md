# `Hypervisor/Lens/AxiomLenses/` — Lean axioms as 213-internal lens choices

★★★ **G12 Tier 4 A2 ENDGAME demonstration** ★★★

The session conversation observation (Mingu, 2026-05-XX):

> "Lean's external axioms (propext, Quot.sound, funext) aren't
>  really external — in 213's worldview, they should also be
>  213-internal results: specific lens choices applied on top of
>  the unique Raw substrate."

This sub-cluster makes that observation explicit by reformulating
each Lean axiom as a 213-internal **lens** that *collapses a
specific raw distinction*.

## Files

  - **`Propext.lean`** — propext as the "iff-equivalent propositions
    collapse" lens
  - **`Funext.lean`** — funext as the "pointwise-equal functions
    collapse" lens
  - **`QuotSound.lean`** — Quot.sound as the "equivalence-class
    collapse" lens

## What this demonstrates

For each Lean axiom A, we provide:

  1. A 213-native **lens definition** showing what raw distinction A
     collapses (a structure-preserving projection / equivalence
     relation)
  2. A pair of theorems showing classical math's reliance on A is a
     **specific lens choice** (one of many possible)
  3. The 213-native PURE alternative that doesn't apply this lens
     (= keeps the distinctions visible)

## Honest scope

These files are **demonstrations**, not a full axiomatic equivalence
proof.  The full claim — "every Lean axiom is derivable as a Raw
catamorphism" — is a much deeper undertaking that would require:

  - A formal Lens object inhabiting `Lens (Raw → Raw / ~_A)` for
    each axiom A
  - A theorem `view_universal_for_A : ∀ A-using theorem, factors
    through that lens`

What we provide here is the **structural commitment** that the
patterns ARE lens choices, with concrete small witnesses.  The
broader formalisation is left as a research direction.

## Connection to session work

The funext-refactor (parts 1-15 + Tier 3) is the *operational
manifestation* of the funext lens being explicit:
  - `_at` variants live in the no-funext-lens view (PURE)
  - function-eq forms live in the funext-lens-applied view (Quot.sound)

These AxiomLenses files are the *theoretical statement* of what
the refactor was doing.

## Connection to research notes

  - **G2** (trajectory principle): propext/Quot.sound collapse
    trajectories; 213 keeps trajectory itself
  - **G3** (Raw as universal trajectory space): every classical
    theory's foundation factors through Raw via some Lens
  - **G11** (Galois at eighty): structural foundations naturally
    precede ZFC; ZFC was historical accident
  - This sub-cluster makes the G2/G3/G11 picture concrete in Lean
