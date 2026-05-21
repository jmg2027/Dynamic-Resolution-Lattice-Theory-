# G101 — Meta-scan synthesis: what 6 scanners actually surfaced

**Date**: 2026-05-21  
**Branch**: `claude/analyze-lean4-ast-patterns-49Rh2`  
**Milestone**: 100 G-documents in the corpus; this branch
contributed G90–G100 (with G87 ceded to parallel branch).

Consolidation of all meta-scan findings on this branch into:
  · Single tooling inventory (§1)
  · Cross-tool convergence map (§2)
  · Final unified abstraction roster (§3)
  · Logical-structure surfaces actually found (§4)
  · Honest assessment of what wasn't found (§5)
  · Process model retrospective (§6)

---

## §1.  Tooling inventory

Six scanners, all built and committed on this branch.  Each
emits a TSV (gitignored) and a stdout report.

| # | Scanner | Layer | Population | Companion doc |
|--:|---------|-------|-----------:|---------------|
| 1 | `tools/ast_fold_scan.py` (+ `_body.lean`) | Tier-2 Expr (elaborated proof terms) | 17,506 consts / 720 fold sites | G90 |
| 2 | `tools/syntax_tactic_scan.py` | Tier-1 syntax (tactic-name sequence) | 3,283 decls / 16,672 tokens | G91 |
| 3 | `tools/syntax_arg_scan.py` | Tier-1.5 (rw / induction / obtain arg-shape) | 7,446 cites + 981 constructs | G92 |
| 4 | `tools/syntax_arg_scan.py --context-target` | Targeted ±N context atlas | 62 rows for Raw.fold_slash | G96 |
| 5 | `tools/syntax_unfold_scan.py` | Tier-1.5+ (`unfold` chunks) | 152 decls / 231 occurrences | G98 |
| 6 | `tools/syntax_rw_cascade_scan.py` | Tier-1.5++ (rw k-grams) | 1,072 decls / 3,993 cites | G99 |
| 7 | `tools/falsifier_mining_scan.py` | Negation-shape catalog | 135 falsifiers / 1,117 decls | G100 |

Plus the shared `tools/lean_syntax_parse.py` (helpers) and the
ad-hoc dep-purity probe used for G95.

**Total Python LOC**: ~1,800.  
**Total research-note LOC**: ~2,400 (G90–G100).  
**Total Lean files added**: 1 (`ast_fold_scan_body.lean`).  
**No PURE theorems added** — this branch is pure meta-analysis.

---

## §2.  Cross-tool convergence map

Where multiple independent scanners pointed at the same thing,
that's the strongest signal.

### Triple-validated outlier: LeibnizAlgLift L1 family

  · **AST (G90)**: identical 5-recursor profile across all 4
    siblings.
  · **Syntax skeleton (G91)**: byte-identical 48-tactic sequence
    × 4 siblings (G91 L1).
  · **Citation graph (G92)**: byte-identical 43-cite multiset
    × 4 siblings (G94 §1 N4 cross-validation).
  · **Deep dive (G94 §8)**: 30-token shared prefix + α/β fork at
    position 30; bidegree knob doesn't affect proof structure.
  · **rw-cascade (G99)**: `h_components × 4` 4-gram appears in
    exactly these 4 siblings + LeibnizAlgLift21.

5 of 7 scanners point at L1.  This is the highest-confidence
abstraction target in the corpus.

### Triple-validated outlier: h_components L2 family

  · **G91 L2**: 32-tactic byte-identical × 4 siblings.
  · **G92 / G94 §8.1**: 12-cite multiset byte-identical × 4
    siblings.  **Tactic sequences are literally identical at
    every position.**
  · L2 is the cleanest possible abstraction — name-only.

### Adoption-gap singleton: mul_left_comm / add_left_comm

  · **G99 rw-cascade**: 25 decls × `[NatHelper.mul_assoc,
    Nat.mul_comm, NatHelper.mul_assoc]` manual rotation; 18
    decls × additive analogue.
  · `NatHelper.mul_left_comm` EXISTS at line 293 but is cited 1
    time in 1,072 rw-citing decls.
  · This is a different KIND of finding from G98's missing
    abstraction — it's an adoption gap.

### Confirmed existing abstractions (no new candidates)

  · `cupList ⊕ deltaList`     → `list_level_leibniz_general`
    (G98 Chunk 1, confirmed by parallel branch)
  · `cupAW ⊕ Cochain.add/zero` → `cupAW_add_*`, `cupAW_zero_*`
    (G98 Chunks 2a/2b)
  · `lensXor ⊕ constLens`      → `boolToConstLens_xor`
    (G98 Chunk 3)
  · `Raw.fold ⊕ Raw.slash`     → `Raw.fold_slash`
    (G98 Chunk 4, G92 hub at 50 callers)
  · `Survives ⊕ residue`       → `alive_iff_clause4_alive`
    (G98 Chunk 6, parallel-branch Pattern #9)

### Pattern #2 universal at multiple layers

  · **AST**: 17 Pell-FSM modular periodicity decls share
    Nat.recAux + decide skeleton (G90 M3).
  · **Syntax**: 37 decls match `[intro, induction, decide,
    show, rw]` tactic template (G91).
  · **Construct shapes**: 80 % of inductions are on Nat-typed
    variables with `zero | succ` (G92).
  · **Falsifier mining**: 8 % of decls are negative `[decide]`
    proofs (G100).

Pattern #2 (decide-finitism) is the single most-corroborated
methodological signature in the corpus.

---

## §3.  Unified abstraction roster

Final priority ordering by combined evidence strength.  Lower
rank = lower confidence or smaller mass.

| Rank | ID | Source | Family | Status | Mass / scope |
|-----:|----|--------|--------|--------|--------------|
| 1 | **L2** | G91 L2 + G94 §8.1 | `h_components_{α,β}` × `Leibniz{21,22}Final` | **fully byte-identical** (32-tactic + 12-cite) | ~96 tactic-tokens, 2 files |
| 2 | **N8** | G99 | `NatHelper.mul_left_comm` adoption gap | mechanical rewrite | ~50 cite-tokens, 8 files |
| 3 | **N9** | G99 | `add_left_comm` adoption gap | mechanical rewrite | ~36 cite-tokens, 8 files |
| 4 | **L1** | G91 L1 + G94 §8.2 + G99 h_components×4 | LeibnizAlgLift × 4 | 30-tok shared prefix + α/β fork | ~117 tokens, 4 files |
| 5 | **C**  | G94 §2 + §7 | CutSumOne × 8 | 9-tok shared opener, 3-component template, universal closer | ~140 tokens, 1 file (+ consumers) |
| 6 | **L**  | G94 §6.2 Sub-2 | Tree-manipulation slash-arm prologue | 5+ siblings, 10-token shared prefix | ~50 tokens, 4 files |
| 7 | **N7** | G98 Chunk 5 | `caseElement` Prism truth table | NEW missing abstraction (2 general lemmas needed) | ~30 LOC, 1 file |
| 8 | **M**  | G94 §6.2 Sub-3 | `Raw.recAux` / `RawBy.recAux` pair | small but deep | minor, 2 files |
| 9 | Pisano L3 | G91 L3 + G94 §8.4 | `pisano_predict_realises_pell_{14,17}` | 20-tactic byte-identical × 2 | small, 2 files |
| 10 | LDD L4 | G91 L4 | `addLDD` / `mulLDD` | 16-tactic byte-identical × 2 | small, 1 file |
| 11 | CDDouble L5 | G91 L5 | `I_mul_J` / `J_mul_I` | 16-tactic byte-identical × 2 | small, 1 file |
| 12 | √N L1-old | G90 M4 | `sqrt{2,3,5}_no_rational_aux` × 4 | AST-level op-multiset identical | medium, 4 files |
| 13 | Σ-fold | G90 M2 | math.Vec.inner = physics.observable_sum | AST byte-identical | cross-domain |
| 14 | XorProj | G90 M6 | `foldr_xor_proj` 3-projection family | **CLOSED by parallel branch** (`798c3a3a`) | — |
| 15 | Pell-FSM | G90 M3 + G91 5-tactic | `pellProperModN_*` × 8 | parametric template | medium, 8 files |

Items 14 and several adjacent are closed.

### Done / closed in cycle

Closed by parallel branch (`subset-bijection-lemmas-w2FKf`):

  · C1 (NatHelper + ListHelper + Int213.Bound centralisation)
  · C2 (foldr_xor_proj absorption)
  · C5 (Pattern #2 quantitative citation)
  · N5 (Nat.max_comm centralisation)
  · N6 (Int.mul_sub / Int.sub_mul centralisation)
  · DRLT is now **PURE-bounded on Lean 4 core** — zero
    non-test DIRTY citations.

Closed on this branch (analysis only):

  · N1 (NatHelper audit) — surfaced, then ceded
  · N2 (Raw.fold_slash atlas) — TSV delivered
  · N3 (a|b|slash 23-decl skeleton)
  · N4 (out-degree × tactic-length cross-validation)
  · G94 §6 — `Tree.swap_*`, `transportTree_*` ladder identified
  · G94 §7 — CutSumOne universal closer (`bool_eq_iff +
    decide_eq_true`) identified

### Open at session end

Items 1-13 on the roster are surfaced but not executed.  All
have characterisation sufficient for a future marathon to pick
up.

---

## §4.  Logical-structure surfaces ACTUALLY found

The user's original question (this session, pre-G94 era):

> "수학 법칙 찾는 알고리즘 혹은 논리 구조 자체에 대한 힌트를
> 보고싶거든."

Honest tally of what the meta-scans surfaced about DRLT's logic.

### Structural-vocabulary observations

  · **5 recursor tags carry the entire corpus** (G90).  DRLT
    proofs = `List.foldl/foldr + Nat.recAux/brecOn + List.rec`.
    No Fin folds, no Array folds, no well-founded recursion, no
    higher-order recursors.  **DRLT lives in a finitist + list-
    structural + Nat-recursive universe.**
  · **18 decls case-split on `a | b | slash`** (G94 §6).
    DRLT-unique trichotomy fingerprint; all 18 directly touch
    the Raw 4-clause axiom.
  · **`Raw.fold_slash` is the universal API surface** (G92 + G94
    §3): 50 distinct callers, all atomic-Raw level.  Clause 4
    enters proofs through a single canonical move.
  · **`E213.Tactic.NatHelper.*` is the load-bearing internal
    infrastructure** (G92 / G95): the most-cited internal
    family.  PURE-shield over Lean-core Nat algebra.

### Quantitative methodology fingerprint

  · **36 % of theorems are pure `[decide]`** (G91): 1,178 of
    3,283 decls.  Pattern #2's footprint quantified.
  · **8 % are decide-verified negative claims** (G100): 135 of
    1,117 tactic-bodied theorem/lemma decls.  DRLT's
    falsifiability surface.
  · **`simp` essentially absent** (0.3 % of tactic tokens) —
    consciously rejected in favour of explicit `rw` chains.
  · **`rw`-cascade dominance**: 17 % of tokens, 4.05 cite
    average per proof, max 43 (G92).
  · **80 % of inductions on Nat-typed variables**; 94 % of
    `with`-blocks are `zero | succ` (G92).

### Negative-knowledge surface

  · **135 auto-discovered falsifiers** (G100) split into 4
    shapes: 78 % `≠`, 15 % `¬ P`, 6 % `¬ ∃`, 1 % `¬ ∀`.
  · **Distinguishability is the dominant negation** —
    consistent with Raw's distinguishability primitive being
    the operational essence of the 4 clauses.
  · **8 structural-impossibility theorems** (`¬ ∃`): chain
    uncountability, universal-morphism non-surjectivity,
    coproduct universal-property failure, swap-matching
    impossibility, etc.  DRLT's bound-from-below
    impossibility lattice.
  · **The Cayley-Dickson tower is a structural negation
    generator** (G100 §"Cayley-Dickson factory"): 16 % of
    falsifiers live in 4 CD files.  Each tower level
    provably loses an algebraic property.

### Cross-domain identifications

  · **`Σ-fold` cross-domain identity** (G90 M2):
    `Linalg213.Gram.Vec.inner` ≡ `Physics.AtomicBase.Observable.observable_sum`
    at the elaborated `Expr` level.  **Math/physics distinction
    is sociological, not logical, at the fold layer.**
  · **`XorPairCombine` ↔ ℤ/2-bilinear projection** (G90 M6):
    248 fold sites reduce to 3 linear projections (`fst`,
    `snd`, `fst⊕snd`) of the same algebraic form — surfaced
    as `foldr_xor_proj` general lemma (closed by parallel
    branch).

---

## §5.  What was NOT found

Equally honest accounting of what this branch's tools did NOT
deliver, relative to the user's original question.

### No theorem-generation algorithm

The original aspiration — *automate the discovery of new
mathematical laws by analysing proof patterns* — was not
achieved.  The scanners are **descriptive of the existing
corpus**, not **generative of new content**.  Each tool can:
  · count occurrences of a pattern,
  · cluster decls sharing a pattern,
  · surface candidates for abstraction.

None can:
  · automatically derive the implicit statement that a tactic
    skeleton instantiates,
  · propose new theorems not already present in the corpus,
  · transfer motifs across formal libraries.

### Implicit-lemma extraction: limited

  · G98 unfold-graph: 1 missing-lemma candidate out of 6 chunks
    (17 % hit).
  · G99 rw-cascade: surfaced 2 adoption gaps (mul_left_comm /
    add_left_comm), not missing-lemma candidates.  Existing
    lemmas were under-used, not absent.
  · G94 ladder analysis: 5 abstraction candidates surfaced,
    all of which the parallel branch had implicit knowledge of.
    None were a "discovery"; all were known to be templated.

The honest reading: the meta-scans operated as **validation
+ catalog** tools rather than **discovery** tools.

### Cross-corpus motif transfer: not attempted

This branch never compared DRLT motifs against Mathlib or
other Lean repos.  Cross-corpus comparison would distinguish
*universal* mathematical patterns from *DRLT-specific*
patterns — but requires network access to external libraries
plus parsing infrastructure.  Deferred.

### Structural-impossibility deepening: not attempted

G100's 8 `not_exists` theorems are deep, but no analysis was
done of *why* they're true — e.g., the proof structure of
`chain_uncountable` was not examined.  Each structural
impossibility could be a separate research thread.

### Counter-factual exploration: not attempted

No scanner asked "what would happen if X were different" —
e.g., the alive predicate was postulated for a while before
its derivation; could other postulates be similarly dissolved?
The dual-branch closed the AliveDerivation gap, but the
methodology of "find postulate → derive it" wasn't generalised
into a scanner.

---

## §6.  Process model retrospective

### What worked

  · **Dual-branch parallelism** (this branch / parallel branch)
    held cleanly through 4 handshake exchanges (G93 → G94 →
    G96 → G97).  No merge conflicts; clear lines of
    responsibility ("meta surfaces, substantive executes").
  · **Soft-offer / counter-ask** pattern: every handshake
    listed soft asks; the other side decided which to action.
    Both branches kept agency.
  · **Ceding G-numbers on collision** (G87, then again at G94)
    avoided narrative confusion.  The convention
    "meta-branch uses higher numbers" emerged organically.

### What didn't

  · **G-number collisions** happened twice (G87, G94) because
    the branches don't fetch each other before naming.  Could
    add a convention "fetch other branch + check next free
    number" to prevent.  Or accept that ceding is cheap.
  · **TSV deliverables sometimes overstated certainty**
    (e.g., the granularity heuristic in C3 returned 0 group-
    level callsites; this was useful but the parallel branch
    needed clarification that the heuristic was conservative).

### Generalising the model

The G97 §6 process note (parallel branch) flagged that the
**"meta surfaces / substantive executes"** division of labour
"generalises to other static-analysis tasks: future audits
(purity-check, layer-audit, lessons-mining, ...) could follow
the same pattern."

This branch's tooling has demonstrated 6 scanner archetypes
that can be re-used:

  1. AST-level Expr motif scanner (Lean meta + Python cluster).
  2. Syntax-level tactic skeleton scanner (regex).
  3. Citation-graph extractor (`rw`/`apply`/`exact` arg parser).
  4. Targeted ±N context dumper.
  5. Multi-def co-occurrence chunk discoverer.
  6. k-gram cascade miner over ordered citations.

Future static-analysis tasks would pick from this archetype set
and customise per question.

---

## §7.  Single takeaway

If a future reader has time for only one thing from this
branch:

> The G91 + G92 + G94 finding that the **L1 LeibnizAlgLift
> 4-sibling ladder is byte-identical at AST, tactic-skeleton,
> AND citation-graph layers simultaneously**.  Three
> independent scanners converged on the same four bytes.
> That triple agreement is the strongest empirical signal of an
> implicit parametric structure that this branch produced.

The L2 (h_components) family follows the same shape with the
additional property that **tactic sequences are literally
identical at every position** across the 4 siblings.

Both are abstraction candidates in the closure-ready pile.

---

## Pointers

  · This branch tip: `73b4c635` (at time of writing).
  · Run any scanner:
    ```
    python3 tools/ast_fold_scan.py
    python3 tools/syntax_tactic_scan.py
    python3 tools/syntax_arg_scan.py
    python3 tools/syntax_arg_scan.py --context-target <lemma>
    python3 tools/syntax_unfold_scan.py
    python3 tools/syntax_rw_cascade_scan.py --k 3 --top 20
    python3 tools/falsifier_mining_scan.py
    ```
  · All accept `--report-only` (where applicable) for fast
    re-clustering.
  · Cross-branch handshake docs: G93, G96 (mine), G94, G97
    (theirs).
