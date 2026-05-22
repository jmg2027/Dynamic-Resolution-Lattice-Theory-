# theory/

Human-readable narrative of the formalized DRLT-213 results.  Mirrors
the directory shape of `lean/E213/Lib/` so a reader can navigate
between code (truth) and prose (explanation) by path.

## Role in the three-tier discipline

| Tier | Where | Purpose |
|---|---|---|
| 1. Scratchpad | `research-notes/` | Working memos |
| 2. **Source of truth** | `lean/E213/` | PURE-verified Lean |
| 3. **This book** | `theory/` | Narrative + Lean references |

A chapter in `theory/` exists only when the corresponding Lean
sub-tree has **closed** per `PROMOTION_CRITERIA.md`.

## Reading order

1. `00_axioms_summary.md` — bridge from `seed/AXIOM/` (axiom spec) to
   the chapters here.  Read this first if you haven't read
   `seed/AXIOM/`.
2. `math/INDEX.md` — math chapters (closed sub-trees only).
3. `physics/INDEX.md` — physics chapters.

## Layout

```
theory/
├── INDEX.md                  ← this file
├── PROMOTION_CRITERIA.md     ← when a Lean sub-tree may be promoted
├── 00_axioms_summary.md      ← bridge to seed/AXIOM/
│
├── math/
│   ├── INDEX.md
│   ├── cohomology/
│   │   └── hodge_conjecture.md   ← promoted 2026-05-21
│   ├── cayley_dickson/           ← (algebra tower — pending)
│   ├── mobius/                   ← (Mobius213 — pending)
│   ├── nat213/                   ← (Nat213 lens fractal — pending)
│   ├── analysis/                 ← (Analysis213 / DyadicSearch — pending)
│   └── pattern_catalog/          ← (G28/G30 — pending)
│
└── physics/
    ├── INDEX.md
    ├── alpha_em/                 ← (α_em precision — pending)
    ├── symmetry/
    │   └── c3_chain.md           ← promoted 2026-05-22 (gauge emergence)
    └── couplings/                ← (TripleCoupling / Basel — pending)
```

## Current chapters (2)

| Chapter | Lean sub-tree | Promoted |
|---|---|---|
| `math/cohomology/hodge_conjecture.md` | `lean/E213/Lib/Math/HodgeConjecture/` | 2026-05-21 |
| `physics/symmetry/c3_chain.md` | `lean/E213/Lib/Physics/Symmetry/` | 2026-05-22 |

## Adding a chapter

1. Check `PROMOTION_CRITERIA.md` — all Hard criteria must pass.
2. Soft criteria need Mingu's judgment.
3. Write the chapter at the mirrored path.
4. Update the relevant `math/INDEX.md` or `physics/INDEX.md`.
5. Move the source research notes to `research-notes/archive/`.
6. Update Lean docstring citations from `research-notes/G##` to
   the new `theory/<path>`.
