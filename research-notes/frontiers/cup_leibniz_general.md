# Cup-Leibniz general — ∀(k,l) self-referential lex-cup

**Status**: open.  Recorded per the `PROCESS.md` frontier-recording rule
(named only in the `theory/math/cohomology/cupaw.md` tail; now tracked here).

## The open problem

The general Cup-Leibniz rule `δ(α ⌣ β) = δα ⌣ β ± α ⌣ δβ` for the
**self-referential lex-cup** at **all** bidegrees `(k, l)` — not just the
specific arities already closed.

## What IS closed (so the frontier is bounded)

The CupAW Leibniz machinery is in place and ∅-axiom PURE
(`lean/E213/Lib/Math/Cohomology/CupAW/`):

- the decomposition layer (`Decomp`, `UniversalLift`,
  `AlgLift{Alpha,Beta}`, `BasisLeibniz`);
- the per-bidegree closures (`Leibniz5_1_2`, `Leibniz5_1_3`,
  `Leibniz5_1_4`, `Leibniz5_3_1`, `Leibniz21Final`, `Leibniz22Final`,
  `UniversalFamilyCapstone`).

## What is OPEN

The **uniform `∀(k, l)`** closure: a single statement (not a finite family
of fixed-bidegree theorems) proving the lex-cup Leibniz identity for every
`(k, l)`.  The fixed-degree closures cover the cases needed downstream; the
parametric-in-`(k,l)` general theorem is not yet assembled.

## Cross-refs

- `theory/math/cohomology/cupaw.md` — the chapter (closed family + this tail)
- `research-notes/frontiers/G35_chiral_cup_ring_catalog.md` — chiral cup ring
