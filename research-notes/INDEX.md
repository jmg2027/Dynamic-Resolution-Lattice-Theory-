# research-notes/

Exploratory notes that fed into the formal Lean library.  Kept as
*record of the path*, not canonical statement.  Source of truth is
`lean/E213/`.

## Layout

```
research-notes/
├── INDEX.md             ← this file
├── 75, 76               ← semantic-atom thesis (active foundational)
├── G1–G5, G12           ← pre-audit insight notes (universal lens,
│                          trajectory, chiral/phase, sublanguage,
│                          layered API)
├── G28, G29, G30        ← corrected output of the G17–G27 audit arc
│                          + pattern catalog synthesis
├── hodge/               ← G6–G11 Hodge program closure cluster (6 notes)
├── audit/               ← G17 empirical pattern audit + G18–G27 iterations
└── archive/             ← closed historical: 17/19/30 + A1/B/C/D/E/F series
```

## Top-level (active reference)

| File | Theme | Status |
|---|---|---|
| `G29_residue.md` | Foundational text — the residue of pointing | **Active** (boot-sequence read) |
| `G28_every_pattern_present.md` | Operational primitives: every stateable pattern lives in 213 | Active (corrects G27) |
| `G30_pattern_catalog_synthesis.md` | Pattern catalog synthesis (metaformalization arc closure) | Active; companions in `Math/PatternCatalog*` |
| `75_semantic_atom.md` | 213 as the atom of meaning + existence | Foundational thesis |
| `76_ultimate_ouroboros.md` | `Prop` instance via `propAsDistinguishing` | Formalization companion to 75 |
| `G1_universal_lens.md` | Universal-lens unification | Closed in `Meta/UniversalLens*.lean` |
| `G2_trajectory_principle.md` | 4-insight unification on Raw trajectory | Cited from `LESSONS_LEARNED.md` |
| `G3_raw_as_universal_trajectory.md` | Raw = free magma on 2 generators (universal trajectory) | Cited from `LESSONS_LEARNED.md` |
| `G4_chiral_phase_duality.md` | d=5 dual views (chiral / phase) | Cited from `HANDOFF.md` |
| `G5_213_as_sublanguage.md` | 213 as the sublanguage of mathematics | Cited from `HANDOFF.md` |
| `G31_minimal_root_lens.md` | Trajectory-as-witness IVT — `ConsistentOracle` readout = minimal-root cut, no locatedness | Skeleton closed in `Math/Analysis/DyadicSearch/MinimalRootLens.lean`; full IVTRoot pending monotone-poly milestone |
| `G35_chiral_cup_ring_catalog.md` | **213-Algebra catalog** — synthesis of Δⁿ cohomology + K_{m,n}^{(c)} bipartite + fractal recursion + resolution-finite arithmetic + Aut/Pisano + meta layers (12 domains).  Five frontier conjectures (C1–C5) | Active; `Lib/Physics/AlphaEM/{CupChannelInventory, ProjectionRatios, ChannelCohomologyLoss, GradedDecomposition, LaplacianSpectrum, PiFiveGap}.lean` instantiate the framework |
| `hodge/` (sub-tree, 6 notes) | Hodge program closure: G6 translation, G7 Lens initiality + cup blueprint, G8 standard-math bridge, G9 HC²¹³ closure, G10 17-theorem programme, G11 Galois historical | Closed in `Math/Cohomology/HodgeConjecture/`; see `hodge/INDEX.md` |
| `G12_layered_api_classification.md` | Layered API classification (Hypervisor) | Cited from `Hypervisor/API.lean`, `OS/INDEX.md` |

## Subdirectories

- **`hodge/`** — G6–G11 Hodge program closure (6 notes).  Reading
  order, Lean closure mapping, framing-correction status all in
  `hodge/INDEX.md`.  Each note is closed in
  `lean/E213/Lib/Math/Cohomology/HodgeConjecture/` (Foundation +
  Bridge + Refinement + Toolkit + Pairing + Structure).

- **`audit/`** — G17 empirical pattern audit (6125 declarations) +
  G18–G27 classification iterations.  Superseded by G28/G29 at the
  conceptual level; raw audit data + tactic catalogues retained as
  evidence base.  See `audit/INDEX.md`.

- **`archive/`** — closed historical exploratory drafts.  Pre-G era
  (17/19/30), kernel cardinality (A1/B1/B2/C1), resolution-limit
  early framing (D1/D2/D3, originally "finitism conviction" — now
  superseded by `seed/RESOLUTION_LIMIT_SPEC.md`), Real213 analysis
  roadmap (E1–E5), Real213 marathon state (F0–F6).  All formalized
  or superseded; preserved as record of path.  See `archive/INDEX.md`.

## Adding a new note

Use next available G prefix (currently G35+).  Once formalized, leave
the note in place with a `→ closed in <Lean module>` marker.
