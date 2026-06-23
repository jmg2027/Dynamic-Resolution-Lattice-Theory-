# `Lens/AxiomLenses/` — Lean axioms as 213-internal lens choices

Lean's external axioms (propext, Quot.sound, funext) are not
really external — in 213 they are residue-internal events.  Each
is a specific Lens choice; applying it is a residue self-pointing,
not a layer placed above Raw.

This sub-cluster reformulates each Lean axiom as a 213-internal
**lens** that *collapses a specific raw distinction*.

## Architecture: Core / Bridges split (2026-05-XX, part 19)

```
AxiomLenses/
  Core/        ← PURE (∅-axiom): the 213-native lens definitions
                 themselves.  These are the funext213 / propext213 /
                 quotSound213 primitives that the rest of 213 uses.
  Bridges/     ← DIRTY-by-design: deliberate Lean ↔ 213 bridges
                 demonstrating that Lean's external axioms ARE
                 lens applications.  Uses Lean's funext / Quot.sound
                 to inhabit the bridge.  Not imported by 213 core.
```

213 core files import only `Core/`.  `Bridges/` is a sealed
metatheoretic demonstration cluster — its DIRTY status is *the
point*: it reads "here, applying Lean's external axiom collapses
this 213-native distinction".

## Files

### `Core/` (PURE — strict ∅-axiom)

  - **`Core/Funext.lean`** — funext213.  `pointwiseEq` predicate,
    refl/symm/trans, `eq_implies_pointwiseEq`, `funextLens` type
  - **`Core/Propext.lean`** — propext213.  `iffEquiv` predicate,
    refl/symm/trans, `view`, `view_kernel`, `eq_implies_iffEquiv`
  - **`Core/QuotSound.lean`** — quotSound213.  `SetoidLens`
    structure, `quotient`, `project`

### `Bridges/` (DIRTY-by-design — sealed)

  - **`Bridges/Funext.lean`** — `funextLens_inhabited` (Lean funext)
  - **`Bridges/QuotSound.lean`** — `sound_lens` (Lean Quot.sound)

  No `Bridges/Propext.lean` — propext is never used inside 213
  (Iff is sufficient for all internal reasoning).

## What this demonstrates

For each Lean axiom A:

  1. A 213-native **lens definition** (in `Core/`) showing what raw
     distinction A collapses — definable PURE without A
  2. The **bridge demonstration** (in `Bridges/`) showing that
     applying Lean's A inhabits the lens at the meta level
  3. The 213-native PURE alternative (cutEq, Iff, Lens.view) that
     doesn't apply this lens (= keeps the distinctions visible)

## Connection to session work

The funext-refactor (parts 1-15 + Tier 3) is the *operational
manifestation* of the funext lens being explicit:
  - `_at` variants live in the no-funext-lens view (PURE) —
    they implement funext213 directly
  - function-eq forms live in the funext-lens-applied view
    (Quot.sound) — they invoke `Bridges.Funext.funextLens_inhabited`

213 core's strict ∅-axiom standard = "use only `Core/`, never
`Bridges/`".  This is *enforceable*: import discipline + scanner.

## Honest scope

These files are **demonstrations + working primitives**.  `Core/`
provides the funext213 / propext213 / quotSound213 primitives
usable by 213 core for strict ∅-axiom theorems.  `Bridges/`
provides the structural commitment that Lean's external axioms
ARE the application of the corresponding lenses.

## Connection to research notes

  - **G2** (trajectory principle): propext/Quot.sound collapse
    trajectories; 213 keeps trajectory itself
  - **G3** (Raw as universal trajectory space): every classical
    theory's foundation factors through Raw via some Lens — not a
    ranking of 213 over ZFC (no exterior, §5.1), just the internal
    fact that ZFC's commitments are one Lens reading of the residue
  - This sub-cluster makes the trajectory picture concrete in Lean
