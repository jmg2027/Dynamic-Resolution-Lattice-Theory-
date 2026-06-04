# Meta-Analysis Scanner Suite

**Status**: Closed (11 scanners committed, ~1,800 LOC Python +
1 Lean meta file; 18 research notes consolidated).

## Overview

The meta-analysis branch (`claude/analyze-lean4-ast-patterns-49Rh2`,
merged as PR #91) built **11 scanners spanning four analysis tiers**
that examine the E213 Lean corpus for hidden structure: implicit
lemmas, abstraction candidates, byte-identical proof families,
dep-purity gaps, falsifier catalogs.

The suite's distinguishing property: **the substantive research
branch was running in parallel**, and the meta scans surfaced
abstraction candidates that the substantive branch then executed.
The meta→substantive handshake→substantive→meta response→meta response on subset bijection→handshake closure cross-branch handshake closed with **zero
DIRTY Lean-core citations** in DRLT (Lean-core dep-purity audit audit).

Net deliverable: ~89 PURE additions across 7 modules, DRLT now
PURE-bounded on Lean 4 core, 14 abstraction candidates surfaced
(action-items registry §2-§5), 135 auto-discovered falsifiers.

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
- **Expr callgraph**: identical 4-layer L1 hub.
- **Raw-depth BFS**: identical 5-layer L1 encapsulation
  depth profile.

Six-layer byte-identical confirmation = **the strongest possible
abstraction signal**.  Implicit-lemma extraction extracted the implicit lemma
structurally: a 30-token shared prefix + α/β fork at position
30 — bidegree knob doesn't affect proof structure.

This is the cleanest empirical demonstration of "multiple
sibling theorems differ only by an instantiation parameter, share
implicit structural lemma."  Open execution target action-items registry §3 L1.

### 2. Three-level "Raw-derived" taxonomy

Distinct chapter: see `raw_derivation_levels.md` for the
conceptual analysis of (α) logical / (β) structural / (γ)
operational meanings of "everything is derived from Raw".

Key finding: (α) and (β) TRUE; (γ) **empirically FALSE** at the
generic-Lean-infrastructure level.  This refines the
understanding of DRLT's architecture.

### 3. 135 auto-discovered falsifiers

`falsifier_mining_scan.py` identified 135 theorems whose
**negation shape** could serve as a DRLT-validation-standard
falsifier — i.e., decidable propositions that would falsify 213
if their negation held.  Per DRLT Validation Standard
(`seed/AXIOM/08_falsifiability.md`), each adds a measurable
proposition.

Catalog raw at `tools/output/falsifier_catalog.tsv` (gitignored);
top entries documented in decide-failure falsifier mining.  Many overlap existing falsifiers
(N_gen = 3, θ_QCD bound); ~70 are novel candidates.

### 4. Lean-core dep purity audit — closure

The Lean-core dep-purity audit confirmed DRLT is **PURE-bounded on
Lean 4 core**: zero non-test DIRTY citations remain after the
meta→substantive handshake→handshake closure handshake closure (C1-C6 + N5-N6 executed by the
parallel substantive branch).

This is the deepest hygiene confirmation: not just "0 sorry,
0 external axiom" but "0 propext-tainted Lean-core dep" beyond
the few sealed-by-design entries.

### 5. Unfold-graph chunks (unfold-graph chunks + implicit-lemma extraction)

`syntax_unfold_scan.py` identified 6 unfold "chunks" — places
where `unfold X at h; unfold Y at h; ...` patterns suggest an
underlying implicit lemma `X_Y_chain : ∀ ..., X = Y` that should
be extracted.  1 / 6 candidates was confirmed structural
(`caseElement` Prism truth-table, action-items registry §2 N7).

### 6. Rw-cascade adoption gap

`syntax_rw_cascade_scan.py` found that `mul_left_comm` and
`add_left_comm` are **underused** despite being available.  ~150
sites could be simplified by adopting them.  Mechanical
candidate action-items registry §2 N8/N9.

## Cross-branch handshake (meta→substantive handshake → handshake closure protocol)

Two branches operated in tandem during the meta-scan work:

- **meta**: `claude/analyze-lean4-ast-patterns-49Rh2` (this branch)
- **substantive**: `claude/subset-bijection-lemmas-w2FKf` (parallel)

The handshake protocol:
1. **Meta surfaces** abstraction candidates (meta→substantive handshake §C1-C5 + N1-N3)
2. **Substantive responds** with execution status
3. **Meta delivers** support artifacts (substantive→meta response addendum atlas)
4. **Substantive executes** the OPEN items (N5/N6/etc.)
5. **Meta confirms closure** via re-scan

Net result: 6 items closed in cycle (C1 NatHelper centralisation,
C2 XorPairCombine lemma, C3 fold_slash atlas, C5 quantitative
numbers, N5 max_comm, N6 mul_sub/sub_mul).

The protocol is the **"meta surfaces, substantive executes"**
division.  Documented in detail at action-items registry §0.

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

## Open frontier

The scanner suite itself is closed.  The follow-on action items
that the scanners surfaced have all been resolved:

  · Mechanical abstractions land as small refactors in the Lean
    source: the Pisano predictor `obtain`-destructure, the
    bilateral LDD branch helpers, the CDDouble basis non-
    commutativity witness via the derived `DecidableEq Lipschitz`,
    `sigmaList` over `List` in `Meta.Tactic.ListHelper`, the
    `DescentBase N` parametric for √N infinite descent, and the
    `bool_or_ladder_iff_with_pack` composer in `BoolOrLadder`.
  · Mid-marathons that initially looked open turned out to be
    substantively closed already (4-sibling Leibniz collapse with
    α / β parametric helpers + four thin corollaries; CutSumOne
    3-component `cutSum_constCut_at` template + eight sibling
    reductions; `mvt_cutPow_unitBracket_{forward,backward}_at`
    flux-MVT parametric; the `pattern10_eq_at` /
    `hodge_involution_pointwise_5` / `leibniz_pointwise_lift`
    cohomology templates).
  · Several scanner-surfaced clusters were determined to be
    **structurally minimal** under further inspection — ring
    extensionality `cases u; cases v; congr` is already two
    lines, `conj_ne_id` picks a per-instance witness so a
    parameterised helper is as verbose as the original,
    Lipschitz `assoc_*` are pure `by decide` (no symbolic body
    to abstract), FractalLevelZeta master theorems are
    `refine ⟨...⟩ <;> decide` on ten-conjunct shape (already
    maximally compact), and the Physics bracket-containment
    proofs are `by decide` on Nat inequalities (the `decide`
    *is* the proof).
  · The remaining mass-reduction target — fully `(n, k, l)`-
    general Leibniz lift — folds into the Cup-Leibniz open conjecture.

Theory documentation lands alongside: a Raw-derivation
three-level taxonomy (`theory/meta/raw_derivation_levels.md`),
plus the four scanner-surfaced patterns (#10 adoption-gap
detection, #11 triple-layer agreement, #12 three-level Raw
derivation, #13 decide-finitism quantitative profile) absorbed
into `LESSONS_LEARNED.md`.

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
- ✅ `theory/meta/raw_derivation_levels.md` (Raw-derivation three-level taxonomy)
