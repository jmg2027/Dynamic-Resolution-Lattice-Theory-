# research-notes/archive/

Closed historical exploratory drafts.  Each is either formalized in
`lean/E213/` or superseded.  Preserved as record of the path that led
to the current formalization.

**Note on N_U framing (post G120 Round 3, 2026-05-22)**: archived
notes here predate the G120 N_U re-derivation work.  Phrases like
"four-domain convergent invariant", "N_U as system invariant",
"4-Lens convergence", and `def universe_level` appear throughout
this archive — these reflect the *pre-G120 framing* that was
retracted on 2026-05-22.  Current canonical reading:
`seed/RESOLUTION_LIMIT_SPEC.md` §2 (G120 Round 3 rewrite) +
`LESSONS_LEARNED.md` 교훈 1+2 (G120 Round 3 rewrite).  Archived
text retained as record of the path; do NOT cite pre-G120 phrasings
as current canon.

## Pre-G era (3 files)

| File | Theme | Now at |
|---|---|---|
| `17_existence_mode_lens.md` | Early lens semantics (existence-mode interpretation) | Cited from `lean/E213/AUDIT.md` §6.5 |
| `19_lens_not_functor.md` | Lens vs functor distinction | Lens framework |
| `30_bool_is_liar_paradox.md` | Bool/liar-paradox interaction | R1–R5 judgment-game (`seed/AXIOM/06_formalization.md` §7) |

## Kernel cardinality (4 files)

| File | Theme | Closed in |
|---|---|---|
| `A1_kernel_cardinality_investigation.md` | Initial investigation | `lean/E213/Term/` |
| `B1_pure_descent_method.md` | Pure descent attack | `Meta/AxiomMinimality` |
| `B2_hermite_direction.md` | Hermite direction attempt | `Meta/AxiomMinimality` |
| `C1_kernel_cardinality_obstruction.md` | The formal block | `Meta/AxiomMinimality` |

## Resolution-limit early framing (3 files)

Originally written under "finitism conviction" framing; superseded by
`seed/RESOLUTION_LIMIT_SPEC.md` (cardinality is a per-Lens output;
`5²⁵ = configCount 2`, one value of the parametric `configCount`
family — G120 Round 3 reframing).

| File | Theme | Closed in |
|---|---|---|
| `D1_zfc_real_as_final_boss.md` | trajectory/exact type-distinction motivation | `Real213.DyadicTrajectory.alwaysTrueUnit_limit_distinct_from_zero` + `RESOLUTION_LIMIT_SPEC.md` §1 |
| `D2_complexity_class_hierarchy.md` | Complexity class hierarchy | Real213 marathon |
| `D3_real213_native_R.md` | Real213-native ℝ proposal | Real213 marathon |

## Real213 analysis roadmap (5 files)

| File | Theme | Closed in |
|---|---|---|
| `E1_real213_analysis_roadmap.md` | Roadmap | Real213 Phase A–H; cited from `guide/14_cohomological_calculus.md` |
| `E2_phase_b_obstruction.md` | Phase B "wall" | Real213 Phase B closure |
| `E3_modulus_kernel_deep_obstruction.md` | Modulus kernel obstruction | Real213 Modulus chain |
| `E4_orderproj_vs_epsilon_n.md` | OrderProj vs ε_n | Real213 ε bounds |
| `E5_213_stays_213.md` | "213 stays 213" — finitist invariance | Real213 marathon principle |

## Real213 marathon final state (7 files)

| File | Theme | Closed in |
|---|---|---|
| `F0_213_native_arithmetic_synthesis.md` | 213-native arithmetic synthesis | Real213 capstones |
| `F1_generic_cut_kernel.md` | Generic cut-kernel | `Real213/CutMul*`, `Real213/CutSum*` |
| `F2_real_as_lens_output.md` | Real as Lens output | Cauchy completion |
| `F3_transcendental_recurrence_lens.md` | Transcendental recurrence | Pisano marathon |
| `F4_marathon_final_state.md` | Marathon final state | Real213 Phase J–O |
| `F5_full_proofs_summary.md` | Full proofs summary | Real213 capstones |
| `F6_general_theorems_state.md` | General theorems state | Real213 capstones |

## G119 marathon (2 files, archived 2026-05-22)

| File | Theme | Closed in |
|---|---|---|
| `G118_marathon_deferred_items.md` | Marathon Part 5 closure log (11 items closed) | absorbed into `theory/math/dyadic_fsm.md` G119 section + `theory/INDEX.md` |
| `G119_pisano_pell5_research_direction.md` | Pisano-period-for-Pell research direction (closed universally in `p` via Phase 3.2/3.3/4) | `theory/math/dyadic_fsm.md` G119 marathon section + `theory/math/modular_arithmetic.md` G119 section (FLT, F_{p²}, Frobenius) |

## Metascan action items + deep dives (10 files, archived 2026-05-22)

Moved into `metascan/` sub-cluster (joining G90-G106) once every
item in the G107 action-items registry reached a final
disposition.  See `metascan/INDEX.md` for the per-note closure
table and `theory/meta/scanner_suite.md` §"Open frontier" for the
narrative summary.

| File | Theme |
|---|---|
| `metascan/G107_action_items_registry.md` | 24-item registry surfaced by G90-G106 (live tracker until 2026-05-22) |
| `metascan/G108_real213_analysis_deep_dive.md` | Real213 sub-tree audit (REAL-1/2 closed via `bool_or_ladder_iff_with_pack`) |
| `metascan/G109_cross_domain_identification_scan.md` | Math ∩ physics Expr-level identification candidates |
| `metascan/G110_fluxmvt_deep_dive.md` | FLUX-1 closed via `mvt_cutPow_unitBracket_*_at` parametric |
| `metascan/G111_cohomology_deep_dive.md` | COH-1/2/3 closed via three universal templates |
| `metascan/G112_hodge_conjecture_deep_dive.md` | Absorbed into `theory/math/cohomology/hodge_conjecture.md` |
| `metascan/G113_dyadic_fsm_deep_dive.md` | Absorbed into `theory/math/dyadic_fsm.md` |
| `metascan/G114_cayley_dickson_deep_dive.md` | CD-1/2/3 declared structurally minimal per G118 |
| `metascan/G115_lib_physics_deep_dive.md` | PHYS-1/2 declared structurally minimal per G118 |
| `metascan/G116_pattern_catalog_deep_dive.md` | Absorbed into `theory/math/pattern_catalog/pattern_catalog.md` |

## Status

Don't read these for current state.  Read instead:
- `lean/E213/` (formal source of truth)
- `../INDEX.md` (current research-notes layout)
- `../G29_residue.md` (current foundational text)
