# research-notes/archive/metascan/ — Meta-Analysis branch (archived)

The meta-analysis branch `claude/analyze-lean4-ast-patterns-49Rh2`
(merged as PR #91 in main) + the G107 action-items registry +
G108-G116 deep-dive applications.  28 research notes total:
foundational scanner suite (G90-G106), action items tracker
(G107), nine sub-tree deep dives (G108-G116), Raw-derivation
conceptual taxonomy (G104).

**Archived in two passes**:
- Scanner suite + Raw-derivation taxonomy promoted to
  `theory/meta/scanner_suite.md` and
  `theory/meta/raw_derivation_levels.md`.
- G107 + G108-G116 archived once every action item in the
  registry reached a final disposition (executed, already-done,
  or structurally infeasible per G118).  The "Open frontier"
  section of `theory/meta/scanner_suite.md` summarises the
  closure status.

## Notes by category

### Scanner suite (Tier 1 + 1.5 + 2 + negation)
| Note | Tier | Scanner |
|---|---|---|
| `G90_ast_fold_motifs.md` | Tier 2 (Expr) | `ast_fold_scan.py` |
| `G91_syntax_tactic_motifs.md` | Tier 1 (syntax) | `syntax_tactic_scan.py` |
| `G92_citation_graph_and_constructs.md` | Tier 1.5 | `syntax_arg_scan.py` |
| `G98_unfold_graph_implicit_lemma_extraction.md` | Tier 1.5+ | `syntax_unfold_scan.py` |
| `G99_rw_cascade_adoption_gap.md` | Tier 1.5++ | `syntax_rw_cascade_scan.py` |
| `G100_decide_failure_mining.md` | Negation | `falsifier_mining_scan.py` |
| `G102_full_expr_callgraph.md` | Tier 2 | `ast_callgraph_scan.py` |
| `G103_raw_depth_and_expr_shape.md` | Tier 2 | `ast_shape_scan.py` |
| `G105_namespace_shape_and_full_recursor_inventory.md` | Tier 2 | `ast_shape_scan.py` (correction of G90) |
| `G106_L1_expr_structure_extraction.md` | Tier 2 deep | `ast_typesig_scan.py` |

### Synthesis
| Note | Theme |
|---|---|
| `G101_metascan_synthesis.md` | Capstone — what 6 scanners actually surfaced |

### Cross-branch handshake (G93 → G97 protocol)
| Note | Direction |
|---|---|
| `G93_handshake_to_subset_bijection_branch.md` | meta → substantive (5 items + 3 N-items) |
| `G94_handshake_response_to_meta_branch.md` | substantive → meta (response) |
| `G94_metascan_addendum.md` | meta → substantive (atlas + N4 cross-validation) |
| `G95_lean_core_dep_purity_audit.md` | meta audit (0 non-sealed DIRTY) |
| `G96_handshake_response_to_subset_bijection.md` | meta's response to substantive's G94 |
| `G97_handshake_closure_zero_dirty.md` | closure confirmation |

### Conceptual
| Note | Theme |
|---|---|
| `G104_raw_derivation_three_levels.md` | (α) logical / (β) structural / (γ) operational taxonomy → promoted to `theory/meta/raw_derivation_levels.md` |

### Action items + sub-tree deep dives (G107 + G108-G116)

| Note | Topic | Closure |
|---|---|---|
| `G107_action_items_registry.md` | 24 actionable items (mechanical / mid-marathons / smaller / deferred) surfaced by G90-G106 | All items closed: 6 executed in Lean (L3/L4/L5/F/E/REAL-1), 4 already substantively done at audit (L1/C/G110 FLUX-1/G111 COH-1-3), 5 structurally infeasible per G118 (CD-1/2/3, PHYS-1, PHYS-2), 1 folded into G86 (L1 (n,k,l)-fully-general) |
| `G108_real213_analysis_deep_dive.md` | REAL-1 (cutMul iff pair), REAL-2 (cutSumAux), REAL-3-6 audits | REAL-1 + REAL-2 closed via `bool_or_ladder_iff_with_pack` composer in `Real213/Sum/BoolOrLadder` |
| `G109_cross_domain_identification_scan.md` | Cross-domain Expr identification candidates (math ∩ physics) | Findings folded into per-sub-tree deep dives |
| `G110_fluxmvt_deep_dive.md` | FLUX-1 (forward/backward unitBracket pair), FLUX-2 (passthrough class audit), FLUX-3 (∀-degree MVT/FTC research) | FLUX-1 closed (parametric `mvt_cutPow_unitBracket_{forward,backward}_at` exists at `Analysis/FluxMVT/FluxMVTPolynomial.lean`); FLUX-3 is research-grade open |
| `G111_cohomology_deep_dive.md` | COH-1 (Prop52/53 pattern_eq_at), COH-2 (Hodge Prop 5_k), COH-3 (Leibniz4Mixed) | All three closed (`pattern10_eq_at`, `hodge_involution_pointwise_5`, `leibniz_pointwise_lift` templates exist; per-instance theorems delegate) |
| `G112_hodge_conjecture_deep_dive.md` | Hodge program deep dive | Absorbed into `theory/math/cohomology/hodge_conjecture.md` |
| `G113_dyadic_fsm_deep_dive.md` | DyadicFSM sub-tree analysis | Absorbed into `theory/math/numbertheory/dyadic_fsm.md` |
| `G114_cayley_dickson_deep_dive.md` | CD-1 (ring ext), CD-2 (conj_ne_id), CD-3 (Lipschitz assoc_*) | All three declared structurally minimal per G118 — `cases u; cases v; congr` is 2 lines, conj_ne_id per-instance witness is irreducible, assoc_* is `by decide` (no body) |
| `G115_lib_physics_deep_dive.md` | PHYS-1 (FractalLevelZeta master), PHYS-2 (bracket-containment) | Both declared structurally minimal per G118 — master theorems are `refine ⟨...⟩ <;> decide` on ~10-conjunct (already maximally compact); bracket-containment is `by decide` on Nat inequalities (the `decide` IS the proof) |
| `G116_pattern_catalog_deep_dive.md` | Pattern-catalog sub-tree analysis | Absorbed into `theory/math/pattern_catalog/pattern_catalog.md` |

## Cross-references

- **`theory/meta/scanner_suite.md`** — promoted narrative for scanners + findings + cross-branch protocol; §"Open frontier" lists the G107-§4 closure status
- **`theory/meta/raw_derivation_levels.md`** — promoted narrative for G104 taxonomy
- `tools/` — 11 scanner scripts (`ast_*`, `syntax_*`, `falsifier_*`, `audit_axioms`)
