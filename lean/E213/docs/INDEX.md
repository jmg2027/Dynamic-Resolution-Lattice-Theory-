# lean/E213/docs/

Maintenance + organization documents for the `lean/E213/` tree.
Distinct from `lean/E213/ARCHITECTURE.md` (ring + layer spec, the
**ground truth** for tree shape).

These files document **how the tree is maintained**, not what it
contains.

## Files

| File | Purpose |
|---|---|
| `CONSOLIDATION_PROTOCOL.md` | 13-step procedure for cleaning up a leaf directory (V1/V2/V3 capstones, Tight/Sharp progressions).  Codified R1–R11 reorganization rules. |
| `HIERARCHICAL_PLACEMENT.md` | Umbrella conventions: every directory has an umbrella file, every umbrella links every constituent file. |
| `PROMOTION_PATTERNS.md` | Three operational patterns for `research-notes/` → `theory/` promotion (multi-note absorption, narrative-from-scratch, mixed-status absorption).  Companion to `theory/PROMOTION_CRITERIA.md` (the gate spec). |

## Status

These documents are **operational reference** — read them when:
- Cleaning up a leaf directory (CONSOLIDATION_PROTOCOL §13-step)
- Adding a new sub-tree (HIERARCHICAL_PLACEMENT umbrella conventions)
- Reorganizing imports or namespace structure (R1–R11)

These are not narrative or theory — for that, see `lean/E213/ARCHITECTURE.md`
or (once promoted) the corresponding chapter in `theory/`.
