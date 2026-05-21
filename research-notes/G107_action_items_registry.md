# G107 — Action items registry (G90-G106 consolidated)

**Date**: 2026-05-21  
**Branch**: `claude/analyze-lean4-ast-patterns-49Rh2`  
**Purpose**: single authoritative list of every actionable
item surfaced by the meta-scan tree (G90-G106).  Use as
entry-point for any executor (this branch in late
"analysis-only" mode, or any successor branch).

Each item:
  · **ID** — unique short code (N# / L# / C# / etc.)
  · **Source** — which G-doc surfaced it
  · **Status** — DONE / OPEN / SURFACED
  · **Scope** — what it changes
  · **Evidence** — how strongly the meta scans support it
  · **Effort** — rough size estimate (sed-mechanical /
    short / medium / marathon)
  · **Blast radius** — how many files touched

---

## §0.  Cross-branch process model

Two branches operated in tandem during G87-G97:

  · **meta** (`claude/analyze-lean4-ast-patterns-49Rh2`) —
    pattern surfacing + scanner tooling + research notes.
  · **substantive** (`claude/subset-bijection-lemmas-w2FKf`) —
    PURE theorem additions, abstraction execution, math
    marathons.

The G93/G96 → G94/G97 handshake loop confirmed the
"meta surfaces, substantive executes" division.

This registry assumes that pattern continues: items marked
OPEN may be picked up by either branch (typically substantive
side for execution; meta side could do small mechanical items
if instructed).

---

## §1.  DONE — closed during the cross-branch cycle

No action required.  Recap for context.

| ID  | Source | Description |
|-----|--------|-------------|
| C1  | G93 §C1     | NatHelper + ListHelper + Int213.Bound helper centralisation |
| C2  | G93 §C2     | `XorPairCombine.foldr_xor_proj` general lemma + 3-corollary bundle |
| C3  | G93 §C3 → G96 §2 | Raw.fold_slash ± 5 tactic context atlas TSV delivered |
| C5  | G93 §C5     | Pattern #2 quantitative numbers cited in LESSONS_LEARNED |
| N1  | G92 / G93 §C1 | NatHelper coverage audit (folded into C1) |
| N2  | G94 §3      | Raw.fold_slash atlas closed (`tools/syntax_arg_scan.py --context-target`) |
| N3  | G94 §6      | `a \| b \| slash` 23-decl skeleton anatomy |
| N4  | G94 §1      | Out-degree × tactic-length × cite-multiset 3-layer cross-validation |
| N5  | G96 §3 → G97 §1 | `Nat.max_comm` → `NatHelper.max_comm` centralisation (5 sites) |
| N6  | G96 §3 → G97 §1 | `Int.mul_sub` / `Int.sub_mul` → `Meta.Int213.{mul_sub, sub_mul}` (12 sites) |
| G (M6) | G90 M6   | `XorPairCombine` foldr-XOR motifs → `foldr_xor_proj` (closed as C2) |

**Net**: ~89 PURE additions, 7 modules cleaned, DRLT now
PURE-bounded on Lean 4 core.  Three-layer methodology
validated across multiple cycles.

---

## §2.  OPEN — MECHANICAL / IMMEDIATE (low effort, clear path)

These are sed-style rewrites or small @[reducible] alias
additions.  No new mathematical content; high mass-reduction
per minute spent.

### N7 — `caseElement` Prism truth-table generalisation
**Source**: G98 Chunk 5  
**Scope**: Add 2 general lemmas (`caseElement_preview_self`,
`caseElement_preview_other`) in `Lens/Instances/Prism.lean`.
Rewrite the 4 existing truth-table theorems (`aPrism_a/b`,
`bPrism_a/b`) as one-line corollaries.  
**Evidence**: G98 unfold-graph chunk discovery (1/6 hit rate).  
**Effort**: ~30 LOC, single file.  
**Blast radius**: 1 file (`Prism.lean`); 4 existing theorem
names preserved as corollaries → zero downstream impact.

### N8 — `NatHelper.mul_left_comm` adoption
**Source**: G99  
**Scope**: Replace 25 manual `rw [NatHelper.mul_assoc,
Nat.mul_comm, NatHelper.mul_assoc]` chains with
`rw [NatHelper.mul_left_comm]`.  Lemma already exists
(NatHelper.lean:293) but cited only once corpus-wide.  
**Evidence**: G99 §1 — top rw 3-gram (25 decls / 48 occurrences).  
**Effort**: mechanical sed; ~25 line-edits.  
**Blast radius**: 8 files (CutSumOne, Cauchy/Euler/Wallis/
MonotonicBounded, Irrational/Sqrt2Cut, Analysis/*, ...).  
**Net**: ~50 cite-tokens saved; rotation lemma becomes visible
hub (currently 1 caller → ~26).

### N9 — `add_left_comm` adoption
**Source**: G99  
**Scope**: Same as N8 for the additive analogue.  Existing
`add_left_comm` in Algebra213 / Int213 / NatHelper, cited
sparingly.  
**Evidence**: G99 — 18 decls × 3-step manual rotation.  
**Effort**: mechanical sed; ~18 line-edits.  
**Blast radius**: 8 files (PellSeq, Meta/Int213/Core,
EncodePair213, LeibnizLex*, CauchySchwarz, InnerProduct).  
**Net**: ~36 cite-tokens saved.

### L2 — `h_components_{α,β}` 4-sibling family
**Source**: G91 L2 / G94 §8.1  
**Scope**: 4 byte-identical tactic sequences (32 tokens × 4)
across `Leibniz{21,22}Final.h_components_{α,β}`.  Add one
parametric `h_components_general`, replace 4 originals with
`@[reducible]` aliases.  
**Evidence**: 3-layer byte-identical (G91 tactic + G92 cite +
shape).  
**Effort**: ~50 LOC.  
**Blast radius**: 2 files (`Leibniz21Final.lean`,
`Leibniz22Final.lean`).  
**Net**: ~96 tactic tokens retired with zero proof rewriting.

### Sub-2 (G94 §6) Tree slash-arm prologue helper
**Source**: G94 §6.2  
**Scope**: 5 decls share `[intro, induction, rfl, rfl, have,
unfold, obtain, obtain, have, have, ...]` 10-token opening:
`Tree.swap_depth/leaves`, `Swap.Tree.swap_swap`,
`transportTree_roundtrip/canonical`.  Candidate: a tactic
macro `tree_induction_slash_unfold` bundling the prologue.  
**Evidence**: G94 §6.2 — 5 siblings sharing 10-token prefix.  
**Effort**: short (~1 tactic macro + 5 callsite refactors).  
**Blast radius**: 3 files (`Levels.lean`, `Swap.lean`,
`RawCmpIndependence.lean`).

---

## §3.  OPEN — MID-SIZE CONSOLIDATIONS

Each requires writing one or two parametric theorems +
@[reducible] aliases.  Substantial mass-reduction.

### L1 — LeibnizAlgLift 4-sibling (BIGGEST single target)
**Source**: G91 L1 + G94 §1/§8.2 + G102 + G103 §3 + G106  
**Scope**: G106 §3 sketches the parametric form.  4
sibling proofs collapse to 2 parametric theorems
(`leibniz_via_α_decomp` + `leibniz_via_β_decomp`) over
`{n k l : Nat}`, with the 4 originals as `@[reducible]`
aliases.  
**Evidence**: **6-layer byte-identical** within each factor-
pair (AST recursor / syntax 48-tokens / cite 43 / Expr
invocations 206,914 / Expr nodes 628,271 / Expr-string
3,309,145 chars).  Cross-pair difference only 0.1 % (factor-
knob binder swap).  Corpus-record overdetermination.  
**Effort**: medium marathon — requires understanding bz5_2
generalisation (parallel branch's FinBridgeGeneral
infrastructure already provides ∀(n, k, l) bridges).  
**Blast radius**: 4 files in `Cup/AW/`.  Downstream consumers
unchanged via aliases.  
**Net**: ~6.6 M chars retired (50 % of L1's elaborated mass).
Largest single mass-reduction surfaced.

### C — CutSumOne 8-sibling (BROADEST by sibling count)
**Source**: G94 §2 + §7  
**Scope**: 8 `cutSum_*` decls in
`Real213/Sum/CutSumOne.lean` share a 9-token templated
opener `[intro, apply, show, constructor, intro, have,
obtain, have, have]` + universal closer (`bool_eq_iff` +
`decide_eq_true`).  3-component template proposed:
opener + per-instance arithmetic body + closer.  
**Evidence**: G94 §7 — `bool_eq_iff` cited by all 8 (1× each),
`decide_eq_true` cited by all 8 (~3× each), 6/8 share
`NatHelper.mul_assoc` + `Nat.mul_comm`.  Tail divergence is
in order, not vocabulary.  
**Effort**: medium marathon (write template + 8 arithmetic
identity discharges).  
**Blast radius**: 1 file + its consumers.  
**Net**: ~50-60 % of CutSumOne family's tactic mass retired
(~140 tokens).

---

## §4.  OPEN — SMALLER CONSOLIDATIONS

### L3 — Pisano Predictor 14/17
**Source**: G91 L3 / G94 §8.4  
**Scope**: 2 byte-identical 20-tactic ladders across
`Predictor14.pisano_predict_realises_pell_14` /
`Predictor17.*_pell_17`.  Parametric form over modulus.  
**Effort**: short.  
**Blast radius**: 2 files.

### L4 — `addLDD` / `mulLDD`
**Source**: G91 L4  
**Scope**: 2 byte-identical 16-tactic ladders in
`Smooth.lean`.  Lens differentiability over `+` and `×`.  
**Effort**: short.  
**Blast radius**: 1 file.

### L5 — `CDDouble.I_mul_J` / `J_mul_I`
**Source**: G91 L5  
**Scope**: 2 byte-identical 16-tactic ladders — Cayley-Dickson
basis non-commutativity witness pair.  
**Effort**: short.  
**Blast radius**: 1 file.

### M (Sub-3) — `Raw.recAux` / `RawBy.recAux` recursor pair
**Source**: G94 §6.2 Sub-3  
**Scope**: 2 sibling theorems sharing 10-token prefix.
Candidate parametric `Raw.recAux_under_relation`.  
**Effort**: short but high-leverage (recursors are deep
infrastructure).  
**Blast radius**: 2 files (`Theory/Raw/Rec.lean`,
`Theory/RawCmpIndependence.lean`).

### E — `sqrt{2,3,5}_no_rational_aux` × 4
**Source**: G90 M4  
**Scope**: 4 `*_no_rational_aux` decls share identical
`Nat.recAux` op-multiset.  Candidate single
`sqrtN_no_rational_aux : ∀ N, ¬ IsPerfectSquare N → ...`.  
**Effort**: medium (need ∀N IsPerfectSquare predicate +
proof).  
**Blast radius**: 4 files (Sqrt2KernelFree, Sqrt2Pure,
Sqrt3Pure, Sqrt5Pure).

### F — Σ-fold cross-domain
**Source**: G90 M2  
**Scope**: `Linalg213.Gram.Vec.inner`, `PhaseRouting.routeSum`,
`Physics.AtomicBase.Observable.{observable_sum,
phase2_observable_summary}`, `FoccSpectrum.focc_spectrum_master`
share fold + HAdd skeleton at Expr level.  Candidate
`sigmaList : (List α) → (α → ℕ) → ℕ` infrastructure.  
**Effort**: short.  
**Blast radius**: 5 files across math + physics.

### Pell-FSM modular periodicity
**Source**: G90 M3 + G91 5-tactic cluster  
**Scope**: 8+ `pellProperModN_period_*` decls share Pattern
#2 `Nat.recAux + decide` skeleton.  Candidate parametric
`pellProperModN_period {N : Nat} (prime_or_atomic : ...) :
period_witness` over N.  
**Effort**: medium.  
**Blast radius**: 8 files (DyadicFSM/Pell/ProperMod{11,13,17,
19,23,29,31,37}).

### ModArith `mod3` / `mod5` family
**Source**: G90 M5  
**Scope**: 6 mod5 + 3 mod3 decls share recursor skeleton
modulo modulus.  Candidate parametric `mod_p_classification`.  
**Effort**: medium.  
**Blast radius**: 2 files (`PureNatMod3.lean`, `PureNatMod5.lean`).

---

## §5.  OPEN — DEFERRED / OPTIONAL

These were noted in passing but require either substantial
extension work or aren't blocking anything.

### Type-DEFINITION dependency closure
**Source**: G104 §1 caveat  
**Scope**: Walk type DEFINITIONS (def-expansion of `Cochain`,
`Cut`, `binom`, etc.) to compute the TRUE transitive Raw-
dependency at the definitional layer.  Would resolve the (γ)
operational-reduction gap noted in G104.  
**Effort**: substantial — new Lean meta scanner.  
**Value**: tightens the "everything from Raw" claim from
"(α) + (β) true" to "(γ) too via def-expansion".

### Sub-expression motif extraction
**Source**: G105 §5 methodological note + G101 §5 deferred  
**Scope**: Hash all Expr subtrees of size ≤ N across the
corpus; cluster by frequency; surface motif candidates.
Would generalise G90's fold-only scanner to ALL applied-head
patterns.  
**Effort**: substantial — new Lean meta or careful Python
analysis on the dumped Expr strings.  
**Value**: could surface implicit lemmas G90 didn't find
because it had a hardcoded recursor list.

### 15 ambiguous Raw.fold_slash rows
**Source**: G96 §2 + G97  
**Scope**: 15 of the 62 Raw.fold_slash callsites had
"ambiguous" granularity heuristic.  Manual inspection could
identify Pattern #9 retrofit candidates.  
**Effort**: short manual pass.  
**Value**: low — the parallel branch's G97 already noted
Pattern #9 opens NEW theorems rather than shortening
existing ones.  Probably yields nothing actionable.

### Refined sort classifier
**Source**: G104 §4  
**Scope**: Improve `walkCodomain` to detect Prop-valued head
symbols (Eq / Iff / ¬ / And / Or / Exists / True / False).
Would shift the 97 % "Other" classification to
`Prop ≈ 98 %, Type ≈ 1.4 %, Sort ≈ 0.6 %`.  
**Effort**: trivial (regex extension).  
**Value**: low (confirmatory only — DRLT being mostly Prop
is already obvious).

### Per-namespace tactic-style audit
**Source**: G105 §1.1 architectural finding  
**Scope**: For each namespace, compute tactic-skeleton
fingerprint (G91 sequences).  Compare Math vs Physics vs
Lens vs Theory to see if proof STYLE varies by layer (not
just shape).  
**Effort**: short (re-cluster G91 data per namespace).  
**Value**: moderate; primarily diagnostic / architectural.

---

## §6.  Tool inventory + reproduction

All 8 scanners live on this branch.  Re-running any of them
regenerates its TSV from current corpus state.

| Tool | Companion doc | Output |
|------|---------------|--------|
| `tools/ast_fold_scan.py` (+ body) | G90 | `_ast_fold_scan_rows.tsv` |
| `tools/syntax_tactic_scan.py` | G91 | `_syntax_tactic_rows.tsv` |
| `tools/syntax_arg_scan.py` | G92 + G96 | `_syntax_arg_cites.tsv`, `_syntax_arg_shapes.tsv` |
| `tools/syntax_arg_scan.py --context-target` | G96 | `research-notes/data/raw_fold_slash_context.tsv` |
| `tools/syntax_unfold_scan.py` | G98 | `_syntax_unfold_rows.tsv` |
| `tools/syntax_rw_cascade_scan.py` | G99 | (no TSV; reuses cites) |
| `tools/falsifier_mining_scan.py` | G100 | `_falsifier_rows.tsv` |
| `tools/ast_callgraph_scan.py` (+ body) | G102 | `_ast_callgraph_edges.tsv` |
| `tools/ast_shape_scan.py` (+ body) | G103 | `_ast_shape_rows.tsv` |
| `tools/ast_typesig_scan.py` (+ body) | G104 | `_ast_typesig_edges.tsv`, `_ast_typesig_sorts.tsv` |
| `tools/ast_l1_dump_body.lean` | G106 | (ephemeral, not committed run-each-time) |

Shared helper: `tools/lean_syntax_parse.py`
(`strip_comments`, `find_decl_bodies`, `walk_e213_files`).

All scanner TSVs are gitignored.  All scanner CODE is committed.
Re-running any scanner: `python3 tools/<scanner>.py`.

---

## §7.  Suggested execution order (if a successor wanted to do it all)

Sorted by (mass-reduction × confidence) / effort.  Top items
first.

  1. **L2** (G91 §L2 / G94 §8.1) — fully byte-identical,
     name-only abstraction.  Quickest win, biggest
     confidence-per-effort.
  2. **N7** (G98 Chunk 5) — Prism truth-table generalisation.
     Surfaces missing structural property.
  3. **N8** + **N9** (G99) — mul/add_left_comm adoption.
     Pure mechanical sed.
  4. **Sub-2** (G94 §6) — Tree slash-arm prologue tactic macro.
     Cleans 5+ Tree-manipulation proofs.
  5. **L3** + **L4** + **L5** — three small 2-sibling
     consolidations.  Quick wins.
  6. **L1** (G106) — biggest single mass-reduction.  Medium
     marathon.  Highest-confidence target.
  7. **C** (G94 §7) — CutSumOne 8-sibling 3-component
     template.  Medium marathon.
  8. **E** (G90 M4) — `sqrtN_no_rational_aux` parametric.
     Medium.
  9. **F** (G90 M2) — Σ-fold cross-domain abstraction.
  10. **M** (G94 §6 Sub-3) — `Raw.recAux` recursor pair.
  11. Pell-FSM + ModArith mod3/5 — medium marathons.

If only one marathon is picked: **L1**.  6-layer
overdetermination at 50 % mass reduction is the cleanest
target.

If only one mechanical item is picked: **L2** — zero proof
rewriting, just name aliasing.

---

## §8.  Process note for successors

  · This branch is **analysis-only** by current convention
    (G93 / G97 handshake).  Items in §2-§5 above should be
    picked up by an executor branch.
  · Cross-branch communication via research-notes/Gxx*.md
    handshake docs has worked.  Future executors should
    reference the G-IDs above when committing.
  · @[reducible] alias preservation of original theorem names
    is the established pattern (per parallel branch's C1
    centralisation).  Use it for all backward-compat needs.
  · Keep the TSVs gitignored; rerun scanners to regenerate.

---

## §9.  Closing observation

11 mechanical / small items + 5 medium marathons + 5
optional extensions.  Executing all would:

  · retire ~7-8 M chars of elaborated proof mass (mostly L1's
    50 %),
  · centralise 5+ infrastructure clusters (NatHelper /
    ListHelper / Int213.Bound + new entries),
  · reduce the L-ladder count from 5 to 0 (all consolidated),
  · close every G94-G106 open item.

The branch's job is to make these items findable and
characterised.  That job is done.
