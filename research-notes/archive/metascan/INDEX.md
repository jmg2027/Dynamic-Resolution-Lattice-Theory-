# research-notes/archive/metascan/ — Meta-Analysis branch (archived)

The meta-analysis branch `claude/analyze-lean4-ast-patterns-49Rh2`
(merged as PR #91 in main).  18 research notes documenting the
11-scanner Python suite + key findings + cross-branch handshake
+ Raw-derivation conceptual taxonomy.

**Archived 2026-05-22**: promoted to:
- `theory/meta/scanner_suite.md` (16 notes consolidated)
- `theory/meta/raw_derivation_levels.md` (G104 standalone)

G107 (action items registry) **stays active** at top-level —
live tracker, not closed narrative.

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

## Cross-references

- **`theory/meta/scanner_suite.md`** — promoted narrative for scanners + findings + cross-branch protocol
- **`theory/meta/raw_derivation_levels.md`** — promoted narrative for G104 taxonomy
- `research-notes/G107_action_items_registry.md` — **still active** at top level (24 actionable items)
- `tools/` — 11 scanner scripts (`ast_*`, `syntax_*`, `falsifier_*`, `audit_axioms`)
