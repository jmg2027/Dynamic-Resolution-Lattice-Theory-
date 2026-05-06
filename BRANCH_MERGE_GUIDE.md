# Branch merge guide

Volatile branch state as of 2026-05-04.  Read before merging
`claude/beilinson-conjecture-port-hg4Jf` into anything else.

## What this branch carries

Meta-work only:

- `CLAUDE.md` — full hierarchical rewrite with boot sequence,
  meta-principle, hard-rules table, failure-modes catalog
- `research-notes/audit/` (G17 audit + G18–G27 iterations) + `research-notes/G28`/`G29`
- `research-notes/G29_residue.md` — clean foundational text
  ("the residue of pointing")
- Cleanup deletions: `G6/G7/G8/G9*.md` + corresponding malformed
  `Bridge/G7Vacuity.lean`, `Bridge/G9ReductioVoid.lean`,
  `Bridge/CohomologyWithoutQuotient.lean` (all dichotomy-importing)
- Merge of `claude/fix-propext-constraints-Rdn1r` session 27 박멸
  work (sealed 251 → 19)

What this branch does **NOT** carry (anymore):

- The Bridge cluster (`lean/E213/Math/Cohomology/HodgeConjecture/Bridge/`)
- The k5 rust binaries (`k5_spinglass`, `k5_decoder`, `k5_discrete_geom`)

These were physically moved to `claude/fix-propext-constraints-Rdn1r`
on 2026-05-04 (commit `0e522c0` on that branch).

## Branch responsibilities

| Branch | Holds |
|---|---|
| `claude/beilinson-conjecture-port-hg4Jf` | meta + CLAUDE.md + research notes |
| `claude/fix-propext-constraints-Rdn1r` | strict ∅-axiom Lean work, including Bridge cluster |
| `main` | (eventual integration target) |

## When merging this branch elsewhere

### If merging into `main` directly

Take everything as-is.  Bridge/ + k5 binaries will *not* arrive from
this branch — they arrive from `claude/fix-propext-constraints-Rdn1r`.
Merge that branch separately (or first).

### If merging this branch into `claude/fix-propext-constraints-Rdn1r`

The CLAUDE.md on `Rdn1r` is the *pre-rewrite* version (319 lines,
session-start preamble at top).  This branch has the post-rewrite
version (boot sequence + meta-principle + hard-rules table).  Take
this branch's CLAUDE.md.

`Rdn1r` will already have Bridge/ + k5 binaries from commit `0e522c0`.
This branch's deletion of those files would *remove* them on merge —
do **not** apply the deletion.  Resolve the file-deletion conflicts by
keeping the `Rdn1r` version (= keeping the Bridge files alive).

In practice: when conflicts appear on Bridge/ files or k5 rust
binaries, choose `--theirs` (the `Rdn1r` side).

### If merging `claude/fix-propext-constraints-Rdn1r` into this branch

Bridge/ files will reappear, which is fine — they were intentionally
moved there for organization, not deleted from the project.

## OS/ — dissolved (M14, 2026-05-06)

The `lean/E213/OS/` orchestration ring was dissolved in M14 Phase A:
  * `OS/HodgeConjecture/Bridges/*` (motivic bridges) →
    `Lib/Math/Cohomology/HodgeConjecture/MotivicBridge/`
  * `OS/Physics/Capstones/*` (5 capstones) →
    `Lib/Physics/Capstones/`
  * Empty `OS/` directory + `OS.lean` umbrella deleted.
  * 1 vacuous duplicate (`BeilinsonRegulator.lean` stub) deleted in
    favour of the substantive Math/Cohomology version.

The merge concern that motivated this section is resolved.  See
`HANDOFF.md` Part 33 for the full M14 timeline.

## Why the split

`claude/fix-propext-constraints-Rdn1r` is the strict-∅-axiom home —
all Lean work that closed the session 27 박멸 (251 → 19 sealed) lives
there, and the Bridge cluster (Beilinson, Galois, Motive↔Étale,
Phase, Ising, Potts, SpinGlass, MLDecoder, DiscreteGeometry) belongs
in the same Lean-side sweep.

`claude/beilinson-conjecture-port-hg4Jf` carries the meta + research
output: the ORIGIN-aware CLAUDE.md, the G-note empirical audit, and
the G29 residue text written after the seed re-read.  No Lean work.

This file itself is part of that meta layer — delete after the two
branches are reconciled.
