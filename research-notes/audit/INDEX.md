# research-notes/audit/

Empirical theorem-pattern audit (G17) and classification iterations
(G18–G27).  All concepts here are **superseded by `G28` + `G29`** at
the top level; raw data + sub-inspections retained as evidence base.

## G17 — empirical audit (21 files)

The audit ran on 6,125 declarations in `lean/E213/`.  Sub-files are
the inspection cuts by tactic / shape:

| File | Cut |
|---|---|
| `G17_audit_raw.csv` | full per-decl data |
| `G17_audit_summary.json` | aggregated stats |
| `G17_pattern_audit.md` | top-level pattern audit |
| `G17_combo_full_distribution.md` | full slot-combo distribution |
| `G17_inspect_capstone.md` | capstones |
| `G17_inspect_def_only.md` | def-only declarations |
| `G17_inspect_equality_*.md` (cases/decide/match/other/rfl/rw) | equality strata |
| `G17_inspect_existential.md` | ∃-shaped |
| `G17_inspect_implication_thm.md` | →-shaped |
| `G17_inspect_universal_thm.md` | ∀-shaped |
| `G17_inspect_omega_users.md` | omega-using |
| `G17_inspect_simp_users.md` | simp-using |
| `G17_inspect_pisano_marathon.md` | Pisano marathon-specific |
| `G17_inspect_pure_parallels.md` | _pure parallel pattern |
| `G17_inspect_top_combos.md` | top tactic combinations |
| `G17_inspect_combos_11_50.md` | combos ranked 11–50 |

## G18–G27 — classification iterations

Successive attempts to extract a meaningful classification axis from
the audit data.  Each was corrected by the next:

| File | Attempt | Corrected by |
|---|---|---|
| `G18_pattern_inspection.md` | Read 256 decls stitch-by-stitch | G19 |
| `G19_equality_strata.md` | 5 equality strata | G20 |
| `G20_migration_boundary.md` | omega/simp/term boundary | G21 |
| `G21_building_blocks.md` | defs / impls / universals | G22 |
| `G22_combo_concentration.md` | 5 shapes = 54% of theorems | G23 |
| `G23_pisano_marathon_anatomy.md` | Inside one marathon | G24 |
| `G24_six_families.md` | 6 functional families (tactic-axis) | **G27 (wrong axis)** |
| `G25_zero_axiom_milestone.md` | _pure parallels architecture | G26 |
| `G26_synthesis.md` | Synthesis of G17–G25 | G27 |
| `G27_trajectory_content_classification.md` | Trajectory-content (18 categories) | **G28 (still keyword-narrow)** |

## What survived

Conceptual axis correction landed at top-level:
- `../G28_every_pattern_present.md` — operational primitives, every stateable pattern in 213
- `../G29_residue.md` — clean foundational text (the residue of pointing)

The audit data itself (G17 raw CSV + JSON + sub-inspections) remains
the evidence base for any future re-classification.
