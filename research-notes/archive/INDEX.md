# research-notes/archive/

Closed historical exploratory drafts.  Each is either formalized in
`lean/E213/` or superseded.  Preserved as record of the path that led
to the current formalization.

## Pre-G era (3 files)

| File | Theme | Now at |
|---|---|---|
| `17_existence_mode_lens.md` | Early lens semantics (existence-mode interpretation) | Cited from `seed/AUDIT_Lean.md` §6.5 |
| `19_lens_not_functor.md` | Lens vs functor distinction | Lens framework |
| `30_bool_is_liar_paradox.md` | Bool/liar-paradox interaction | R1–R5 judgment-game (`seed/AXIOM.md` §7) |

## Kernel cardinality (4 files)

| File | Theme | Closed in |
|---|---|---|
| `A1_kernel_cardinality_investigation.md` | Initial investigation | `lean/E213/Kernel/` |
| `B1_pure_descent_method.md` | Pure descent attack | `Meta/AxiomMinimality` |
| `B2_hermite_direction.md` | Hermite direction attempt | `Meta/AxiomMinimality` |
| `C1_kernel_cardinality_obstruction.md` | The formal block | `Meta/AxiomMinimality` |

## Resolution-limit early framing (3 files)

Originally written under "finitism conviction" framing; superseded by
`seed/RESOLUTION_LIMIT_SPEC.md` (cardinality is a per-lens output;
N_U = 5²⁵ is a four-domain convergent invariant).

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

## Status

Don't read these for current state.  Read instead:
- `lean/E213/` (formal source of truth)
- `../INDEX.md` (current research-notes layout)
- `../G29_residue.md` (current foundational text)
