# theory/PROMOTION_CRITERIA.md

When may a Lean sub-tree be promoted to a `theory/` chapter?

A sub-tree `X` is **promotable** iff it satisfies all **Hard** criteria
(mechanically checkable) AND the author judges it satisfies all
**Soft** criteria.

## Hard criteria (mechanical)

### H1 — ∅-axiom standard
```
tools/scan_axioms.py <X-umbrella>  →  0 DIRTY, 0 sorry, 0 external axiom
```
Every theorem in `X` must report `#print axioms …  →  "does not depend
on any axioms"`.  Pre-existing DIRTY in `X` blocks promotion until
fixed or hard-justified.

### H2 — Build clean
```
cd lean && lake build E213.<X-umbrella>  →  Build completed successfully
```
The umbrella file must exist (per `lean/E213/docs/HIERARCHICAL_PLACEMENT.md`
R2) and build without errors.

### H3 — Architectural placement
`lean/E213/ARCHITECTURE.md` lists `X` in a ring layer (Term / Theory /
Lens / Meta / Lib).  No "homeless" sub-tree.

### H4 — Catalog presence
Core results of `X` appear in at least one of:
- `STRICT_ZERO_AXIOM.md` (PURE catalog)
- `catalogs/constants.md` / `catalogs/precision_results.md` /
  `catalogs/falsifiers.md` (for physics)

If `X` has no quantitative content, this criterion is auto-satisfied.

## Soft criteria (author judgment)

### S1 — Categorical closure
The core meanings of the sub-tree are all present in `X`.  Nothing
material is hosted elsewhere that should belong here.  No "this
should really be in `X` but we put it in `Y` for now" leftovers.

Operational check: if a downstream consumer of `X` cites a result,
the result lives in `X` (not in a sibling sub-tree).

### S2 — Downstream-ready
Other sub-trees can cite `X` results without further preparation —
no name conflicts to resolve, no required prior import, no API drift.

Operational check: at least one downstream module already cites `X`
in production, or the API surface is documented enough that a future
downstream can.

### S3 — Research-note closure
Every G-note in `research-notes/` that informed `X` is either:
- Absorbed into the chapter being written, or
- Archived (moved to `research-notes/archive/`)

No open research note remains in `research-notes/` top-level for the
`X` topic.  If something is genuinely open (e.g., a conjecture), it
appears in the chapter's "Open frontier" section.

## Chapter structure (template)

```markdown
# theory/<path>/<chapter>.md

## Overview
One paragraph: what is closed here, in 213-native operational terms.

## Lean source
- Umbrella: `lean/E213/<X>.lean`
- Files: <list, with line counts>
- ∅-axiom status: <0 DIRTY, N PURE>

## Narrative
<the actual exposition — what the theorems say, why they hold, how
they fit together.  Lean theorem citations inline.>

## Key results
| Theorem | Lean module | Statement (informal) |
|---|---|---|
| ... | ... | ... |

## Research-note provenance
List of G-notes / archived notes that fed this chapter.

## Open frontier (if any)
What is *not* closed here.  Pointer to research-notes if active.

## How to verify
```bash
cd lean && lake build E213.<X-umbrella>
python3 tools/scan_axioms.py <X-path>
```
```

## Demotion (rare)

A chapter is **demoted** (moved back from `theory/` to `research-notes/`)
if any Hard criterion later breaks:
- H1 broken by axiom regression
- H2 broken by build failure not fixed within one session
- H3 broken by ARCHITECTURE.md change that removes `X`

Demotion preserves git history; rename the file with a deprecation
header.  Avoid by maintaining build hygiene continuously.

## First promotion (2026-05-21)

`math/cohomology/hodge_conjecture.md` — Hodge program closure.
- H1 ✅ (Math/Cohomology/HodgeConjecture/ all PURE)
- H2 ✅ (`lake build E213.Math.Cohomology` clean)
- H3 ✅ (Lib ring, Cohomology sub-tree in ARCHITECTURE.md)
- H4 ✅ (results in STRICT_ZERO_AXIOM.md HC²¹³ section)
- S1–S3 ✅ (research-notes/hodge/ 6 notes absorbed; archived)
