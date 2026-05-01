# research-notes/ — exploratory drafts (numbered series)

Chronological / thematic exploratory notes that **fed into** the
formal Lean library.  Most claims here are now formalized in
`lean/E213/` — these notes preserve the *thought process*, not
the canonical statement.

## Numbered series

| Series | Theme | Status |
|---|---|---|
| `17`, `19`, `30` | Early lens / paradox notes | Historical |
| `75`, `76` | Semantic atom / ouroboros — late-2025 reflections | Historical |
| `A1` | Kernel cardinality investigation | Closed in `lean/E213/Kernel/` |
| `B1`, `B2` | Pure descent + Hermite direction (D-attack on cardinality) | Inputs to AxiomMinimality |
| `C1` | Kernel cardinality obstruction — the formal block | Closed in `Meta/AxiomMinimality` |
| `D1` | "ZFC real as final boss" — finitist conviction | Now `LESSONS_LEARNED.md` 교훈 1 |
| `D2`, `D3` | Complexity class hierarchy + Real213-native R proposal | Inputs to Real213 marathon |
| `E1` – `E5` | Real213 analysis roadmap, obstructions, "213 stays 213" | Real213 marathon Phase A-H |
| `F0` – `F6` | 213-native arithmetic synthesis, marathon final state | Real213 marathon Phase J-O capstones |
| `G1` | Universal lens unification | Lens framework synthesis |

## Reading order

For *historical* understanding (how DRLT got here): chronological by
prefix → 17, 19, 30, 75, 76, A1, B1, B2, C1, D1, D2, D3, E1...

For *current* state: don't read these.  Read instead:
  - `HANDOFF.md` (current snapshot)
  - `CAPSTONE_INDEX.md` (theorem map)
  - `LESSONS_LEARNED.md` (guardrails)
  - `lean/E213/` (formal source of truth)

## Status of each note

Most notes describe **already-closed** problems or **superseded**
roadmaps.  Specifically:

  - `D1_zfc_real_as_final_boss.md`: formalized as
    `Real213.DyadicTrajectory.alwaysTrueUnit_limit_distinct_from_zero`
  - `E1_real213_analysis_roadmap.md`: roadmap completed via Real213
    Phase J-O capstones in `lean/E213/Research/`
  - `F6_general_theorems_state.md`: state superseded by capstones
    (`Real213CutMulConstSum`, `Real213CutSumGeneral` etc.)
  - `G1_universal_lens.md`: closed in `Meta/UniversalLens*.lean`

## When to add a new research note

When a new exploratory direction starts that may or may not
formalize.  Use next available prefix (currently `H1` or `100`+).

Once formalized, **leave the note in place** with a "→ closed in
<Lean module>" marker.  Don't delete — the note is the historical
record of the *path*, not the conclusion.
