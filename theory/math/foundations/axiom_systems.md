# Classical axiom systems as Lens readings on Raw

**Status**: Closed (4 files).

## Overview

Fragments of the classical foundations — Peano arithmetic, ZFC
extensionality, classical-analysis completeness — are realized as
**concrete Lens constructions on Raw**.  They are not alternatives
beneath or above 213, and Raw is not a foundation they rest on: each
is one more Lens reading of the same residue (no exterior,
`seed/AXIOM/05_no_exterior.md` §5.1).

## Lean source

- **Sub-tree**: `lean/E213/Lib/Math/Foundations/AxiomSystems/` (4 files)
- **∅-axiom status**: PURE

## Narrative

The "layered" ring partition (Term → Theory → Lens → Meta → Lib) of
`lean/E213/ARCHITECTURE.md` is a **compile-time dependency** ordering,
not a foundation-vs-derivation ranking.  The chapters below read
classical axiom *fragments* through that same Lens machinery:

- **Peano** (`PeanoAsLensComposition`) — `succ`/`zero`/`+` are the
  count-Lens `Lens.leaves` on the Raw chain: `succ_zero_view`,
  `one_plus_one_view`.  The Lens is not injective
  (`peano_lens_not_injective`) — the count is a reading, not Raw itself.
- **ZFC extensionality** (`ZFCExtensionalityAsLens`) — `memberView` and
  `extEquiv` realize the extensionality fragment as a decidable
  predicate on `Raw`; not full ZFC, the extensionality clause only.
- **Classical-analysis completeness** (`ClassicalAnalysisCompletenessAsLens`)
  — Cauchy-sequence equivalence on `Nat → Raw`, completeness read as a
  Lens, not imported.
- **Cross-theory cohabitation** (`CrossTheoryCohabit`) — the Peano count
  and the depth reading cohabit on one Raw (`cohabit_peano_depth`):
  distinct foundations are distinct Lenses on the same residue.

These are the realized fragments; the broader "every axiom system is a
Lens composition" reading is the programme they instantiate, not a
closed all-systems result.

## Connection

- `theory/math/foundations/cross_domain_unification.md` — extends the
  same reading to further paradigm domains
