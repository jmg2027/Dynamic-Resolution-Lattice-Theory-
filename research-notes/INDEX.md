# research-notes/

Exploratory notes that feed the formal Lean library (`lean/E213/`) and
the narrative book (`theory/`).  Record of the path + active scratchpad —
not canonical statement.

## The research cycle

```
  frontiers/<topic>/   ──(work)──▶   lean/E213/  ∅-axiom closure
        │                                  │
        │                                  ▼  (promote, PROMOTION_CRITERIA.md)
        │                            theory/<chapter|essay>
        ▼                                  │
  archive/<topic>/   ◀──────────────────────┘  (source note moves here)
```

Top-level holds **only** this index + the process ledgers.  Everything
in motion lives under `frontiers/` (grouped by topic; see
`frontiers/INDEX.md` — the open board).  Everything closed lives under
`archive/` (grouped by topic; record of the path, cited by nothing).

## Three-tier discipline (canonical: `theory/INDEX.md`)

| Tier | Where | Purpose | Lifetime |
|---|---|---|---|
| 1. Scratchpad | `research-notes/` | Working memos, half-baked ideas | Volatile — once closed, moves to `archive/` |
| 2. Source of truth | `lean/E213/` | PURE-verified formal mathematics | Permanent |
| 3. Theory book | `theory/` | Narrative, mirrors `lean/E213/Lib/` by path | Permanent |

Tier-1 notes may use `G##` chronological prefixes freely (scratch is
volatile, so CLAUDE.md "no session-number in long-lived names" doesn't apply).

## Process ledgers (top-level, human-reviewed)

| File | Theme |
|---|---|
| `promotion_essay_log.md` | Append-only log of promotion-ㄱ / essay-ㄱ triggers + the situation that prompted each — reviewed to pattern-ize when promotion/essay should happen.  Appended by the `process` + `essay` skills. |

## Subdirectories

- **`frontiers/`** — the live open-frontier board, grouped by topic
  (π non-holonomicity, Markov/Lagrange, spiral-axis, completability,
  sequence-depth, PDE estimates, Ricci core, transcendentals,
  + standalones incl. the `G35` 213-Algebra field catalog).  See
  `frontiers/INDEX.md`.
- **`archive/`** — where a closed topic's source notes move when its
  frontier is promoted (see the cycle above).  `foundations/` holds the
  early foundational/lens arc (residue, universal lens, trajectory,
  flat ontology, reading-equivalence RFC — permanent homes:
  `seed/AXIOM/`, `theory/lens/`, `lean/E213/Lens/`); flat files are
  closed cross-domain notes + registries (e.g.
  `RERESEARCH_n_u_removal.md`, the `5²⁵ = N_U`-deletion registry).
- **`audit/`** — G17 empirical pattern audit + G18–G27 classification (raw data retained).
- **`data/`** — raw evidence (`probes/`).

## Adding a note / running the cycle

1. New open question → a note under `frontiers/<topic>/` (or a new topic
   subdir + an entry in `frontiers/INDEX.md`).
2. Once formalized in Lean, leave a `→ closed in <Lean module>` marker.
3. When a topic fully closes, promote it (`theory/PROMOTION_CRITERIA.md` +
   `lean/E213/docs/PROMOTION_PATTERNS.md`) and `git mv` its notes to
   `archive/<topic>/`.  Remove the topic from `frontiers/INDEX.md`.
