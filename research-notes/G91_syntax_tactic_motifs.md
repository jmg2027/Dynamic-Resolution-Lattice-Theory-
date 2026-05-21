# G91 — Tier-1 syntax-level tactic-block scan of E213

**Date**: 2026-05-21  
**Branch**: `claude/analyze-lean4-ast-patterns-49Rh2`  
**Tool**: `tools/syntax_tactic_scan.py`  
**Companion**: `G87_ast_fold_motifs.md` (Tier-2 / Expr level)  
**Scanned**: 780 `.lean` files under `lean/E213/`, 3,283 decls with
tactic bodies, 16,672 whitelisted tactic tokens.

---

## Method

Walk all `.lean` files, strip block + line comments, find each
`<kw> <name> ... := by <body>` block at top level (where `kw ∈
{theorem, lemma, def, example, instance}`), and tokenise tactics
from a 60-name whitelist.  Cluster theorems by:

  (A) full tactic sequence in order
  (B) tactic-name frequency histogram
  (C) `(first, last)` tactic pair
  (D) adjacent-tactic bigrams
  (E) sequence-length distribution

---

## Tactic frequency — 7 tactics carry 81 % of all uses

| Tactic    |  Count |   %  |
|-----------|-------:|-----:|
| `rw`      |  2 889 | 17.3 |
| `have`    |  2 668 | 16.0 |
| `exact`   |  2 290 | 13.7 |
| `decide`  |  2 214 | 13.3 |
| `show`    |  1 493 |  9.0 |
| `rfl`     |  1 093 |  6.6 |
| `intro`   |  1 038 |  6.2 |

Tail (notable rarities for an "induction-heavy" corpus):

| Tactic        | Count |   %  |
|---------------|------:|-----:|
| `induction`   |   281 |  1.7 |
| `simp`        |    48 |  0.3 |
| `omega`       |    61 |  0.4 |
| `linarith`/`ring`/`nlinarith` | 0 | — |

**Reading**: E213's proof culture is *decide + rewrite*, not
*simp + omega + ring*.  `induction` appears in only 1.7 % of all
tactic tokens; the structural recursion lives in `Nat.recAux` /
`Nat.brecOn` terms (G90), often invoked indirectly through
`decide` and pre-computed bases rather than via the `induction`
tactic.

---

## Tactic-sequence length distribution

| len | count | bar (relative) |
|----:|------:|-----|
|   1 | 1 261 | `##################################################` |
|   2 |   418 | `################` |
|   3 |   300 | `###########` |
|   4 |   214 | `########` |
|   5 |   201 | `#######` |
|   6 |   151 | `#####` |
|   7 |   113 | `####` |
|  ≥8 |   625 | (tail to len ≥ 48) |

**38 % of all theorems are length-1**, of which 93 % are pure
`decide`.  This quantifies Pattern #2's footprint precisely:
**1,178 theorems are one-shot `decide` proofs** (≈ 36 % of the
entire corpus).

---

## Top exact-sequence clusters

| count | sequence | example decls |
|------:|----------|---------------|
| 1 178 | `[decide]` | `leaves_equates`, `bool_not_involutive`, ... |
|   153 | `[refine, decide]` | `and_truth_table`, `or_truth_table` |
|    74 | `[rw]` | `tier_slash_from_inputs`, `mod_add_comm` |
|    54 | `[show, rw]` | `abLens_sym`, `pairCombine_comm` |
|    43 | `[intro, show, rw]` | `F9.mul_comm`, `pairHasDistinguishing` |
|    38 | `[show, exact]` | `npairEquiv_refl`, `qpairEquiv_refl` |
|    37 | `[intro, induction, decide, show, rw]` | `pellFSMmod53_run_period_54`, `pellFSMmod59_run_period_29`, ... |
|    32 | `[rw, exact]` | `add_mod_left_pos`, `chartChain_value_mod` |
|    31 | `[intro, exact]` | `leaves_not_refines_*`, `depth_not_refines_*` |
|    30 | `[show, rw, exact]` | `toNat_add`, `value_pos` |
|    15 | `[show, decide, decide, cases, decide, rfl]` | `decomp_step_at_{0,1,2,...}` |
|    14 | `[apply, ext, exact, exact]` | `add_assoc'`, `add_comm'`, `add_zero'` |
|    13 | `[intro, rw, exact]` | `idLens_injective`, `swapLens_injective` |
|    13 | `[cases, cases, congr]` | `ext` |

The **5-tactic Pell-FSM template** (`[intro, induction, decide,
show, rw]`) covers 37 distinct theorems — confirming G90's M3 at
the syntax layer.  AST and syntax agree on the same family.

---

## Bigrams (adjacent tactic pairs)

| bigram | count |
|--------|------:|
| `have → have` | 1 033 |
| `rw → exact`  |   800 |
| `have → rw`   |   721 |
| `show → rw`   |   690 |
| `rw → rw`     |   528 |
| `rw → have`   |   355 |
| `exact → exact` |   317 |
| `decide → decide` |   239 |
| `rw → show`   |   226 |
| `intro → have` |   214 |

**Two dominant micro-strategies**:

  1. **Have-stack-and-close**: `have a; have b; have c; ...; exact h`
     (1 033 `have → have`, 217 `have → exact`).
  2. **Rewrite cascade**: `rw [..]; rw [..]; rw [..]; exact h`
     (528 `rw → rw`, 800 `rw → exact`).

The third — `cases → rfl` (196 occurrences) — is the
decide-replacement when one needs explicit structural cases.

---

## Boilerplate ladders (highest-priority abstraction targets)

Sequences of length ≥ 16 that appear in **multiple distinct
decls** are smoking-gun copy-paste — exact 48-tactic ladders
shared between 2-4 sibling theorems.

### L1 — LeibnizAlgLift family — 48-tactic ladder, x4

```
  · Cohomology/CupAW/LeibnizAlgLift.lean        :: leibniz_via_β_decomp_lens
  · Cohomology/CupAW/LeibnizAlgLift22.lean      :: leibniz_via_β_decomp_22
  · Cohomology/CupAW/LeibnizAlgLift21Alpha.lean :: leibniz_via_α_decomp_21
  · Cohomology/CupAW/LeibnizAlgLift22Alpha.lean :: leibniz_via_α_decomp_22
```
Identical 48-tactic sequences differ only in bidegree (21 vs 22)
and which factor (α vs β) is decomposed.  A single parametric
`leibniz_via_factor_decomp : ∀ (degree : Nat × Nat) (factor : α∣β), ...`
would replace four hand-instantiated copies.
**Abstraction candidate A.**

### L2 — Leibniz{21,22}Final.h_components — 32-tactic ladder, x4

```
  · Cohomology/CupAW/Leibniz21Final.lean :: h_components_α
  · Cohomology/CupAW/Leibniz21Final.lean :: h_components_β
  · Cohomology/CupAW/Leibniz22Final.lean :: h_components_α
  · Cohomology/CupAW/Leibniz22Final.lean :: h_components_β
```
Same as L1 but for the final-form decomposition.  Four copies of
identical 32-step proof.  **Abstraction candidate B.**

### L3 — Pisano Predictor — 20-tactic ladder, x2

```
  · DyadicFSM/Pisano/Predictor14.lean :: pisano_predict_realises_pell_14
  · DyadicFSM/Pisano/Predictor17.lean :: pisano_predict_realises_pell_17
```
Same 20-tactic proof structure, modulus 14 vs 17.
**Abstraction candidate C.**  Note: the file naming
`Predictor{N}.lean` already signals templating intent.

### L4 — Smooth differentials — 16-tactic ladder, x2

```
  · Analysis/Differentiation/Smooth.lean :: addLDD
  · Analysis/Differentiation/Smooth.lean :: mulLDD
```
Both Lens differentiable maps proven by the same 16-tactic
`[intro, show, apply, intro, apply, intro, apply, exact, ...]`
chain — likely should be one lemma about Lens differentiability
applied to + and ×.  **Abstraction candidate D.**

### L5 — CDDouble I_mul_J / J_mul_I — 16-tactic ladder, x2

```
  · CayleyDickson/Tower/CDDouble.lean :: I_mul_J
  · CayleyDickson/Tower/CDDouble.lean :: J_mul_I
```
Cayley-Dickson basis non-commutativity witness pair.
Same 16-tactic skeleton.  **Abstraction candidate E.**

---

## AST × Syntax cross-validation

Patterns surfaced independently at both layers:

| Pattern | AST evidence (G90) | Syntax evidence (G91) |
|---------|--------------------|----------------------|
| Pell-FSM modular periodicity | M3: 8 decls share `Nat.recAux` op-multiset | x37 share `[intro, induction, decide, show, rw]` |
| Cup-Leibniz lex (α/β decomp) | Cup tree dominates `List.foldr` motifs | L1-L2: 8 decls share 32-48 tactic ladders |
| Decide-driven proof culture | n/a (term level) | 36 % of decls are pure `[decide]` |
| Module-local universals | "modal pattern" (G90 §Cross-cutting) | x37 Pell-FSM, x4 LeibnizAlgLift, x4 h_components |

Where AST + Syntax agree on a templated family, the abstraction
opportunity is high-confidence — both the elaborated term and the
human-written tactic body match across instances.

Where they disagree (e.g., `induction` rare at syntax layer but
`Nat.recAux` dominant at AST layer), the elaborator has hidden the
structural recursion behind a `decide` discharge — a stylistic
choice rather than a missed abstraction.

---

## Updated abstraction roster (G90 + G91 combined)

Listed in **priority order by combined evidence strength**:

  · **A. Leibniz factor-decomp** (G91 L1) — 4 copies of a
    48-tactic ladder.  Highest copy-paste cost.  Single
    parametric lemma over `(bidegree, factor)`.
  · **B. Pell-FSM modular periodicity** (G90 M3 + G91 x37 cluster)
    — 8+ recursors at AST, 37+ syntax instances.  Parametric
    `pellProperModN_period N` lemma.
  · **C. √N irrationality** (G90 M4) — 4 copies of
    `Nat.recAux` shape; syntax not yet inspected for these.
  · **D. Σ-fold cross-domain** (G90 M2) — 5 decls share fold
    skeleton across math + physics.
  · **E. XorPairCombine ↔ ℤ/2-bilinear projection** (G90 M6).
  · **F. ModArith mod3 / mod5 family** (G90 M5).
  · **G. Pisano Predictor templating** (G91 L3) — 2 copies of
    20-tactic ladder.
  · **H. LDD smooth differential** (G91 L4) — 2 copies of
    16-tactic ladder, +/× duplication.
  · **I. Cayley-Dickson I-J / J-I witness pair** (G91 L5).

---

## Methodological observation

Two surprising findings from cross-layering:

  1. **`simp` is essentially absent** (0.3 % of tokens).  The
     E213 proof culture has rejected the `simp` style entirely
     in favour of explicit `rw` chains.  This is a deliberate
     stylistic choice — `simp` brings hidden axiom dependencies
     and unpredictable rewriting, while `rw` is exact.  The
     0-axiom standard punishes `simp`.

  2. **`have`-stacking is the dominant micro-pattern** (1 033
     adjacent `have → have`).  Proofs are built bottom-up by
     accumulating named hypotheses, then closing with `exact`.
     This is essentially Curry-Howard-style explicit term
     construction in tactic notation — close to writing the
     proof term by hand.  Consistent with the
     "minimum-assumption, explicit-witness" doctrine.

These are *culture* observations more than abstraction
opportunities, but they help calibrate what counts as idiomatic
DRLT style.

---

## Artifact map

  * `tools/syntax_tactic_scan.py` — Tier-1 scanner (Python only)
  * `tools/_syntax_tactic_rows.tsv` — extracted rows (gitignored)

Run `tools/syntax_tactic_scan.py` to re-execute; `--report-only`
re-clusters cached rows without re-scanning.
