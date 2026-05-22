# Meta-Analysis Scanner Suite

**Status**: Closed (11 scanners committed, ~1,800 LOC Python +
1 Lean meta file; 18 research notes consolidated).
**Promoted from research-notes**: 2026-05-22.

Pattern 1 (multi-note absorption) with a destination variant:
the closed work is **Python tooling under `tools/`**, not a Lean
library under `lean/E213/Lib/`.  The chapter mirrors `tools/` instead
of `lean/E213/Lib/`.

## Overview

The meta-analysis branch (`claude/analyze-lean4-ast-patterns-49Rh2`,
merged as PR #91) built **11 scanners spanning four analysis tiers**
that examine the E213 Lean corpus for hidden structure: implicit
lemmas, abstraction candidates, byte-identical proof families,
dep-purity gaps, falsifier catalogs.

The suite's distinguishing property: **the substantive research
branch was running in parallel**, and the meta scans surfaced
abstraction candidates that the substantive branch then executed.
The G93→G94→G96→G97 cross-branch handshake closed with **zero
DIRTY Lean-core citations** in DRLT (G95 audit).

Net deliverable: ~89 PURE additions across 7 modules, DRLT now
PURE-bounded on Lean 4 core, 14 abstraction candidates surfaced
(G107 §2-§5), 135 auto-discovered falsifiers (G100).

## Source

- **Scanners** (11 Python + 1 Lean meta):
  - `tools/ast_fold_scan.py` (+ `ast_fold_scan_body.lean`)
  - `tools/ast_callgraph_scan.py`, `ast_shape_scan.py`, `ast_typesig_scan.py`
  - `tools/syntax_tactic_scan.py`, `syntax_arg_scan.py`,
    `syntax_unfold_scan.py`, `syntax_rw_cascade_scan.py`
  - `tools/falsifier_mining_scan.py`
  - `tools/audit_axioms.py`, `lean_syntax_parse.py`
- **Total Python LOC**: ~1,800
- **Total Lean meta**: 1 file (`ast_fold_scan_body.lean`)

## Tier organization

| Tier | What it examines | Scanners | Population |
|---|---|---|---:|
| **Tier 1** (syntax) | Tactic-block token sequences | `syntax_tactic_scan.py` | 3,283 decls / 16,672 tokens |
| **Tier 1.5** (citation graph) | rw / induction / obtain arg-shape | `syntax_arg_scan.py` | 7,446 cites + 981 constructs |
| **Tier 1.5+** (unfold chunks) | `unfold X at Y` patterns | `syntax_unfold_scan.py` | 152 decls / 231 occurrences |
| **Tier 1.5++** (rw k-grams) | `rw [...]; rw [...]` cascades | `syntax_rw_cascade_scan.py` | 1,072 decls / 3,993 cites |
| **Tier 2** (Expr) | Elaborated proof terms | `ast_fold_scan.py`, `ast_callgraph_scan.py`, `ast_shape_scan.py`, `ast_typesig_scan.py` | 17,506 consts / 720 fold sites |
| **Negation** | Falsifier shape catalog | `falsifier_mining_scan.py` | 135 falsifiers / 1,117 decls |

Each scanner emits a `.tsv` (gitignored) + a stdout report.  Used
by `--report-only` flag for re-running without touching the repo.

## Key findings

### 1. The L1 LeibnizAlgLift quadruple (cross-tier convergence)

Six independent scanners pointed at the same outlier — the
`LeibnizAlgLift` family of 4 sibling theorems in
`Lib/Math/Cohomology/Cup/`:

- **AST fold scan** (Tier 2): identical 5-recursor profile across
  all 4 siblings.
- **Syntax tactic scan** (Tier 1): byte-identical 48-tactic
  sequence × 4 siblings.
- **Citation graph** (Tier 1.5): byte-identical 43-cite multiset
  × 4 siblings.
- **rw cascade** (Tier 1.5++): identical `h_components × 4`
  4-gram in exactly these 4 + LeibnizAlgLift21.
- **Expr callgraph** (G102): identical 4-layer L1 hub.
- **Raw-depth BFS** (G103): identical 5-layer L1 encapsulation
  depth profile.

Six-layer byte-identical confirmation = **the strongest possible
abstraction signal**.  G106 extracted the implicit lemma
structurally: a 30-token shared prefix + α/β fork at position
30 — bidegree knob doesn't affect proof structure.

This is the cleanest empirical demonstration of "multiple
sibling theorems differ only by an instantiation parameter, share
implicit structural lemma."  Open execution target G107 §3 L1.

### 2. Three-level "Raw-derived" taxonomy (G104)

Distinct chapter: see `raw_derivation_levels.md` for the
conceptual analysis of (α) logical / (β) structural / (γ)
operational meanings of "everything is derived from Raw".

Key finding: (α) and (β) TRUE; (γ) **empirically FALSE** at the
generic-Lean-infrastructure level.  This refines the
understanding of DRLT's architecture.

### 3. 135 auto-discovered falsifiers (G100)

`falsifier_mining_scan.py` identified 135 theorems whose
**negation shape** could serve as a DRLT-validation-standard
falsifier — i.e., decidable propositions that would falsify 213
if their negation held.  Per DRLT Validation Standard
(`seed/AXIOM/04_falsifiability.md`), each adds a measurable
proposition.

Catalog raw at `tools/output/falsifier_catalog.tsv` (gitignored);
top entries documented in G100.  Many overlap existing falsifiers
(N_gen = 3, θ_QCD bound); ~70 are novel candidates.

### 4. Lean-core dep purity audit (G95) — closure

The G95 dep-purity audit confirmed DRLT is **PURE-bounded on
Lean 4 core**: zero non-test DIRTY citations remain after the
G93→G97 handshake closure (C1-C6 + N5-N6 executed by the
parallel substantive branch).

This is the deepest hygiene confirmation: not just "0 sorry,
0 external axiom" but "0 propext-tainted Lean-core dep" beyond
the few sealed-by-design entries.

### 5. Unfold-graph chunks (G98 + G106)

`syntax_unfold_scan.py` identified 6 unfold "chunks" — places
where `unfold X at h; unfold Y at h; ...` patterns suggest an
underlying implicit lemma `X_Y_chain : ∀ ..., X = Y` that should
be extracted.  1 / 6 candidates was confirmed structural
(`caseElement` Prism truth-table, G107 §2 N7).

### 6. rw-cascade adoption gap (G99)

`syntax_rw_cascade_scan.py` found that `mul_left_comm` and
`add_left_comm` are **underused** despite being available.  ~150
sites could be simplified by adopting them.  Mechanical
candidate G107 §2 N8/N9.

## Cross-branch handshake (G93 → G97 protocol)

Two branches operated in tandem during the meta-scan work:

- **meta**: `claude/analyze-lean4-ast-patterns-49Rh2` (this branch)
- **substantive**: `claude/subset-bijection-lemmas-w2FKf` (parallel)

The handshake protocol:
1. **Meta surfaces** abstraction candidates (G93 §C1-C5 + N1-N3)
2. **Substantive responds** with execution status (G94)
3. **Meta delivers** support artifacts (G94 addendum atlas)
4. **Substantive executes** the OPEN items (N5/N6/etc.)
5. **Meta confirms closure** via re-scan (G96, G97)

Net result: 6 items closed in cycle (C1 NatHelper centralisation,
C2 XorPairCombine lemma, C3 fold_slash atlas, C5 quantitative
numbers, N5 max_comm, N6 mul_sub/sub_mul).

The protocol is the **"meta surfaces, substantive executes"**
division.  Documented in detail at G107 §0.

This protocol generalizes: any future meta-analysis branch can
follow the same surfacing → handshake → closure cycle.

## Reproduction

All scanners are `--report-only` capable.  Re-running:

```bash
# Tier-2 Expr scans
python3 tools/ast_fold_scan.py
python3 tools/ast_callgraph_scan.py
python3 tools/ast_shape_scan.py
python3 tools/ast_typesig_scan.py

# Tier-1 syntax + Tier-1.5 citation graph
python3 tools/syntax_tactic_scan.py
python3 tools/syntax_arg_scan.py

# Tier-1.5+ unfold + Tier-1.5++ rw cascade
python3 tools/syntax_unfold_scan.py
python3 tools/syntax_rw_cascade_scan.py

# Falsifier catalog
python3 tools/falsifier_mining_scan.py
```

TSVs land in `tools/output/` (gitignored).  Stdout summaries match
the reports in the archived G-notes.

## Research-note provenance

13 notes archived to `research-notes/archive/metascan/`:

| Note | Theme |
|---|---|
| `G90_ast_fold_motifs.md` | AST fold/recursor motif scan |
| `G91_syntax_tactic_motifs.md` | Tier-1 syntax tactic block scan |
| `G92_citation_graph_and_constructs.md` | Citation graph & tactic-construct shapes |
| `G93_handshake_to_subset_bijection_branch.md` | Meta→substantive handshake |
| `G94_handshake_response_to_meta_branch.md` | Substantive→meta response (1 of 2) |
| `G94_metascan_addendum.md` | N4 cross-validation + fold_slash atlas (2 of 2) |
| `G95_lean_core_dep_purity_audit.md` | Lean-core purity (0 DIRTY) |
| `G96_handshake_response_to_subset_bijection.md` | Meta's response to substantive's G94 |
| `G97_handshake_closure_zero_dirty.md` | Handshake closure confirmation |
| `G98_unfold_graph_implicit_lemma_extraction.md` | 6 unfold chunks, 1 confirmed |
| `G99_rw_cascade_adoption_gap.md` | mul/add_left_comm under-adoption |
| `G100_decide_failure_mining.md` | 135 auto-discovered falsifiers |
| `G101_metascan_synthesis.md` | This chapter's primary source (capstone) |
| `G102_full_expr_callgraph.md` | Full Expr-level callgraph, 4-layer L1 |
| `G103_raw_depth_and_expr_shape.md` | Raw-depth BFS + Expr-shape density |
| `G105_namespace_shape_and_full_recursor_inventory.md` | Per-namespace Expr-shape + recursor |
| `G106_L1_expr_structure_extraction.md` | L1 LeibnizAlgLift Expr extraction (deepest) |

G104 promoted to separate chapter `theory/meta/raw_derivation_levels.md`
(conceptual taxonomy, distinct from scanner-suite findings).

G107 (action items registry) **stays active** as
`research-notes/G107_action_items_registry.md` — it's a live
tracker of executable items, not a closed narrative.

## Open frontier

The scanner suite itself is closed.  Open follow-up work is
tracked in **G107 action items registry** (~14 OPEN items in
§2-§5, ranked by mass × confidence / effort in §7).

Mechanical (≤ 1 day each): N7 (Prism), N8/N9 (mul/add_left_comm
adoption), Sub-2 (Tree macro), L2 (zero-rewrite alias).

Mid-marathons (multiple sessions): L1 6-layer byte-identical
extraction (~6.6M chars retired = 50% L1 mass), C (CutSumOne
3-component).

Smaller (1-3 days): L3 Pisano, L4 LDD, L5 CDDouble, M Raw.recAux
pair, E sqrtN, F Σ-fold, Pell-FSM, ModArith.

Theory documentation (§10): pattern #10-#13 drafts (4 patterns),
4 catalogs, 4 standalone theory docs (highest value: TH-2
Raw-derivation three levels — now closed as
`theory/meta/raw_derivation_levels.md`), 4 navigation updates.

## How to verify

```bash
# Verify all scanners still produce output
for tool in ast_{fold,callgraph,shape,typesig} syntax_{tactic,arg,unfold,rw_cascade} falsifier_mining; do
  python3 tools/${tool}_scan.py --help > /dev/null 2>&1 \
    && echo "OK: $tool" || echo "FAIL: $tool"
done

# Verify Lean-core purity still holds
python3 tools/audit_axioms.py
```

Expected: all scanners exist + work; purity audit reports zero
non-sealed DIRTY citations.

## Citation guidance

- ✅ `theory/meta/scanner_suite.md` (this chapter; scanner suite + findings)
- ✅ `theory/meta/raw_derivation_levels.md` (G104 conceptual taxonomy)
- ✅ `research-notes/G107_action_items_registry.md` (active OPEN items)
- ✅ archived G-notes for deep dives:
  `research-notes/archive/metascan/G##_*.md`
