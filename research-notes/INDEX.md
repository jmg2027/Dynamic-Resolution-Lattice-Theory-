# research-notes/

Exploratory notes that fed into the formal Lean library.  Kept as
*record of the path*, not canonical statement.  Source of truth is
`lean/E213/`.

## Layout

```
research-notes/
├── INDEX.md             ← this file
├── 75, 76               ← semantic-atom thesis (active foundational)
├── G1–G12               ← pre-audit insight notes
├── G28, G29             ← corrected output of the G17–G27 audit arc
├── audit/               ← G17 empirical pattern audit + G18–G27 iterations
└── archive/             ← closed historical: 17/19/30 + A1/B/C/D/E/F series
```

## Top-level (active reference)

| File | Theme | Status |
|---|---|---|
| `G29_residue.md` | Foundational text — the residue of pointing | **Active** (boot-sequence read) |
| `G28_every_pattern_present.md` | Operational primitives: every stateable pattern lives in 213 | Active (corrects G27) |
| `75_semantic_atom.md` | 213 as the atom of meaning + existence | Foundational thesis |
| `76_ultimate_ouroboros.md` | `Prop` instance via `propAsDistinguishing` | Formalization companion to 75 |
| `G1_universal_lens.md` | Universal-lens unification | Closed in `Meta/UniversalLens*.lean` |
| `G2_trajectory_principle.md` | 4-insight unification on Raw trajectory | Cited from `LESSONS_LEARNED.md` |
| `G3_raw_as_universal_trajectory.md` | Raw = free magma on 2 generators (universal trajectory) | Cited from `LESSONS_LEARNED.md` |
| `G4_chiral_phase_duality.md` | d=5 dual views (chiral / phase) | Cited from `HANDOFF.md` |
| `G5_213_as_sublanguage.md` | 213 as the sublanguage of mathematics | Cited from `HANDOFF.md` |
| `G6_hodge_213_translation.md` | Hodge translation strategy | Cited from `Math/Cohomology/HodgeConjecture/Foundation/*` |
| `G7_lens_initiality_cup_blueprint.md` | Lens initiality + cup-product blueprint | Cited from `Foundation/LensCata.lean` |
| `G8_hodge_213_bridge_to_standard_math.md` | Bridge to standard cohomology | Hodge work |
| `G9_hodge_conjecture_complete.md` | Hodge conjecture closure narrative | Hodge work |
| `G10_post_hodge_program.md` | Post-Hodge program sketch | Hodge work |
| `G11_galois_at_eighty.md` | Galois angle | Hodge work |
| `G12_layered_api_classification.md` | Layered API classification (Hypervisor) | Cited from `Hypervisor/API.lean`, `OS/INDEX.md` |

## Subdirectories

- **`audit/`** — G17 empirical pattern audit (6125 declarations) +
  G18–G27 classification iterations.  Superseded by G28/G29 at the
  conceptual level; raw audit data + tactic catalogues retained as
  evidence base.  See `audit/INDEX.md`.

- **`archive/`** — closed historical exploratory drafts.  Pre-G era
  (17/19/30), kernel cardinality (A1/B1/B2/C1), finitism conviction
  (D1/D2/D3), Real213 analysis roadmap (E1–E5), Real213 marathon
  state (F0–F6).  All formalized or superseded; preserved as record
  of path.  See `archive/INDEX.md`.

## Adding a new note

Use next available G prefix (currently G30+).  Once formalized, leave
the note in place with a `→ closed in <Lean module>` marker.
