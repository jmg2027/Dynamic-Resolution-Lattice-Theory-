# lean/E213/docs/

Maintenance + organization documents for the `lean/E213/` tree.
Distinct from `lean/E213/ARCHITECTURE.md` (ring + layer spec, the
**ground truth** for tree shape).

These files document **how the tree is maintained**, not what it
contains.

## Files

| File | Purpose |
|---|---|
| `CONSOLIDATION_PROTOCOL.md` | 13-step procedure for cleaning up a leaf directory (V1/V2/V3, Phase capstones, Tight/Sharp progressions).  Codified R1–R11 reorganization rules.  Derived from the 2026-05-05 FamousCoincidences consolidation. |
| `HIERARCHICAL_PLACEMENT.md` | Post-M11 final-state audit: every directory has umbrella file, every umbrella links every constituent file.  §6 "deferred-28" inventory (now closed). |

## Status

Both documents are **operational reference** — read them when:
- Cleaning up a leaf directory (CONSOLIDATION_PROTOCOL §13-step)
- Adding a new sub-tree (HIERARCHICAL_PLACEMENT umbrella conventions)
- Reorganizing imports or namespace structure (R1–R11)

These are not narrative or theory — for that, see `lean/E213/ARCHITECTURE.md`
or (once promoted) the corresponding chapter in `theory/`.

## Migration note (2026-05-21)

These files lived at `research-notes/CONSOLIDATION_PROTOCOL.md` and
`research-notes/HIERARCHICAL_PLACEMENT.md` until 2026-05-21.  Moved
here because they are Lean-tree maintenance docs, not exploratory
research notes.  Citations updated:
- `lean/E213/ARCHITECTURE.md` §10 R10
- `lean/E213/Lib/Math.lean` umbrella §Status
- `lean/E213/Lib/Math/DyadicFSM.lean` §Status
- `lean/E213/Lib/Physics/Basel/Bound.lean` consolidation note
- `lean/E213/Lib/Physics/Couplings/TripleCoupling.lean` consolidation note
