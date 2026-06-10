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

Top-level holds **only** the boot-sequence anchors + process ledgers
(`INDEX.md`, `promotion_essay_log.md`).  Everything in motion lives under
`frontiers/` (grouped by topic; see `frontiers/INDEX.md` — the open board).
Everything closed lives under `archive/` (grouped by topic; record of the
path).

## Three-tier discipline (canonical: `theory/INDEX.md`)

| Tier | Where | Purpose | Lifetime |
|---|---|---|---|
| 1. Scratchpad | `research-notes/` | Working memos, half-baked ideas | Volatile — once closed, moves to `archive/` |
| 2. Source of truth | `lean/E213/` | PURE-verified formal mathematics | Permanent |
| 3. Theory book | `theory/` | Narrative, mirrors `lean/E213/Lib/` by path | Permanent |

Tier-1 notes may use `G##` chronological prefixes freely (scratch is
volatile, so CLAUDE.md "no session-number in long-lived names" doesn't apply).

## Top-level — anchors (boot-sequence + sustained reference)

| File | Theme |
|---|---|
| `G29_residue.md` | The residue of pointing (boot-sequence, read every session) |
| `75_semantic_atom.md` | 213 as the atom of meaning + existence |
| `76_ultimate_ouroboros.md` | `Prop` instance via `propAsDistinguishing` |
| `G1_universal_lens.md` | Universal-lens unification |
| `G2_trajectory_principle.md` | 4-insight unification on the Raw trajectory |
| `G3_raw_as_universal_trajectory.md` | Raw = free magma on 2 generators |
| `G4_chiral_phase_duality.md` | d=5 dual views (chiral / phase) |
| `G5_213_as_sublanguage.md` | 213 as a sublanguage of mathematics |
| `G12_layered_api_classification.md` | Layered API classification (Lens ring) |
| `G35_chiral_cup_ring_catalog.md` | 213-Algebra catalog (17 domains; §0.5 tracks promotions) |
| `2026-05-18_lens_emergence_path.md` | Lens-emergence + flat-ontology spec (cited from `lean/` + `seed/`) |
| `G152_residue_self_covering.md` | Residue self-covering (cited by CLAUDE.md "View promoted to identity") |
| `RERESEARCH_n_u_removal.md` | Registry of the `5²⁵ = N_U`-as-resolution deletion |
| `RFC_reading_equivalence_primitive.md` | Accepted+implemented RFC (cited by `Lens/{ReadingEquiv,SemanticAtom}.lean`) |
| `G200_action_A_distance1_crossline_separate.md` | Markov kernel: orbit / µ-ν lift of trace-SEPARATE (partial advance + boundary) |
| `G201_action_b_even_markov_family.md` | Markov kernel: even `2·pᵏ` family of the c-uniform realizability lift, closed ∅-axiom |
| `G202_zhang_3c_pm2_roadmap.md` | Markov kernel: Zhang `3c±2` criterion roadmap (composite/even ω=3) |
| `G203_reframe_archetype_modulus_shift.md` | The `3c±2` modulus shift compiled to the 213 stack — +REFRAME lift archetype |
| `G205_cross_domain_conquests_compilation.md` | Cross-domain conquests lowered onto the proof-ISA (L3 → L1) |

## Process ledgers (top-level, human-reviewed)

| File | Theme |
|---|---|
| `promotion_essay_log.md` | Append-only log of promotion-ㄱ / essay-ㄱ triggers + the situation that prompted each — reviewed to pattern-ize when promotion/essay should happen.  Appended by the `process` + `essay` skills. |

## Subdirectories

- **`frontiers/`** — the live open-frontier board, grouped by topic
  (π non-holonomicity, Markov/Lagrange, spiral-axis, completability,
  sequence-depth, + standalones).  See `frontiers/INDEX.md`.
- **`archive/`** — where a closed topic's source notes move when its
  frontier is promoted (see the cycle above).  Currently empty; git
  history retains the path, and it repopulates as future frontiers close.
- **`audit/`** — G17 empirical pattern audit + G18–G27 classification (raw data retained).
- **`data/`** — raw evidence (`probes/`).

## Adding a note / running the cycle

1. New open question → a note under `frontiers/<topic>/` (or a new topic
   subdir + an entry in `frontiers/INDEX.md`).
2. Once formalized in Lean, leave a `→ closed in <Lean module>` marker.
3. When a topic fully closes, promote it (`theory/PROMOTION_CRITERIA.md` +
   `lean/E213/docs/PROMOTION_PATTERNS.md`) and `git mv` its notes to
   `archive/<topic>/`.  Remove the topic from `frontiers/INDEX.md`.
