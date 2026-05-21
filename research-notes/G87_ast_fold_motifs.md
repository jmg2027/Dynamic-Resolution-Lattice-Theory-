# G87 — AST fold/recursor motif scan of the E213 corpus

**Date**: 2026-05-21  
**Branch**: `claude/analyze-lean4-ast-patterns-49Rh2`  
**Tool**: `tools/ast_fold_scan.py` + `tools/ast_fold_scan_body.lean`  
**Inputs scanned**: 17,506 `E213.*` constants with proof terms,
across 1,032 cached `.olean` modules  
**Sites found**: 720 fold/recursor application sites  
**Status**: Tier-2 (Expr-level) analysis complete; findings below.

---

## Method

For every `ConstantInfo.value?` of every constant `E213.*`, walk the
elaborated `Expr` and emit one row per argument of every fold /
recursor application.  Skeletons are normalised
(strip `mdata`, alpha-rename binders, collapse `fvar`/`mvar`/sort
universes, drop `Expr.const` universe levels).  Step-function arg
position is `argIdx = 2` for all five recursor tags observed.

Two clustering metrics:

  * **Strict**: SHA-1 hash of the canonical skeleton string.
    Counts as "same motif" only if the elaborated step is literally
    identical post-normalisation.
  * **Loose**: multiset of operator constants appearing in the
    step body (typeclass `inst*` and `ofNat` filtered out).
    Counts as "same motif" if the same operators are mixed,
    independent of arg/bvar wiring.

---

## Recursor vocabulary

The entire corpus uses only **5 recursor / fold tags**:

| Tag           | Sites |  % |
|---------------|------:|---:|
| `List.foldr`  | 248   | 34 |
| `List.foldl`  | 168   | 23 |
| `Nat.brecOn`  | 152   | 21 |
| `Nat.recAux`  | 150   | 21 |
| `List.rec`    |   2   | <1 |

Not observed in proof terms: `List.recOn`, `Nat.rec`, `Nat.recOn`,
`Nat.fold`, `Fin.*`, `Array.*`, `*foldlM`/`*foldrM`.

**Structural takeaway**: DRLT proofs are List-fold + Nat-structural.
No higher-order recursors, no well-founded recursion, no Fin or Array
folding.  This is a very narrow proof vocabulary for a corpus of
17,506 decls — the codebase has converged on a small primitive set.

---

## Strict-hash clustering

357 distinct strict-hash motifs.  Coverage histogram:

| #decls per motif | #motifs |
|-----------------:|--------:|
| 1                | 349     |
| 2                | 3       |
| 3                | 3       |
| 4                | 1       |
| 12               | 1       |

98 % of strict motifs are single-decl — meaning literal Expr
identity is too tight a similarity metric.  Useful signal lives in
the loose layer below.

The single 12-decl motif is `List.foldl` with op = `#2` (bvar 2):
the polymorphic abstract foldl whose step is supplied externally.
It appears in 12 `_cstage1` compiler-generated bodies (DyadicFSM
runners, ThueMorse, Beilinson regulator, Ising router, ML decoder).

---

## Loose-cluster findings (operator multiset, ≥ 2 decls)

### M1 — Polymorphic foldl (step bound externally)
**16 decls, 52 sites, ops = ∅** (only bvars).  
This is the abstract fold whose step is a parameter, used by
`_cstage1` bodies and by `Delta.Pointwise.foldl_step_eq`.  
*Interpretation*: the universal "list reduction over a generic
algebra" shape.  Already factored.

### M2 — Σ-fold (`HAdd.hAdd` only)
**5 decls, 20 sites** — crosses math and physics:
```
  · Linalg213.Gram.Vec.inner
  · HodgeConjecture.Bridge.PhaseRouting.routeSum
  · Physics.AtomicBase.Observable.observable_sum
  · Physics.AtomicBase.Observable.phase2_observable_summary
  · Physics.Simplex.FoccSpectrum.focc_spectrum_master
```
*Interpretation*: scalar Σ over List Nat.  Each callsite re-derives
the same skeleton — a `sigmaList : (List α) → (α → ℕ) → ℕ`
abstraction would unify all five.  **Abstraction candidate #1.**

### M3 — Pell-Proper modular FSM family
**8 decls, ops = {`Decidable.decide`, `Nat.decLt`, `LT.lt`,
`pellProperFSMmod`, `ArithFSM2.run`}**
```
  · pellProperMod{11,13,17,19,23,29,31,37}_run_period_*
```
*Interpretation*: pure Pattern #2 universal — `Nat.recAux` over an
arithmetic-FSM run with decide-checked transitions.  All 8 decls
share an identical recursor skeleton, varying only by prime modulus
and period.  Templated rewrite would collapse them into one
`∀ N period, period_witnessed → pellProperMod_run_period`
parametric theorem.  **Abstraction candidate #2.**

### M4 — √N irrationality family
**4 decls, ops = {`HAdd`, `HMul`, `LE`}**
```
  · Sqrt2KernelFree.sqrt2_no_rational_aux
  · Sqrt2Pure.sqrt2_no_rational_aux
  · Sqrt3Pure.sqrt3_no_rational_aux
  · Sqrt5Pure.sqrt5_no_rational_aux
```
*Interpretation*: identical `Nat.recAux` skeleton for the
"no rational satisfies p² = N · q²" descent.  Currently duplicated
per `N ∈ {2, 3, 5}`.  A single
`sqrtN_no_rational_aux : ∀ N, ¬IsPerfectSquare N → ¬∃ p q, q ≠ 0 ∧ p² = N · q²`
should replace the family.  **Abstraction candidate #3.**

### M5 — ModArith mod3 / mod5 trichotomy / quintichotomy
**6 mod5 + 3 mod3 decls** — share recursor skeleton
`{HAdd, HMul, mod_p}`, differ only in modulus.  Templated
`mod_p_classification : ∀ p, prime_or_atomic p → ...`.
**Abstraction candidate #4.**

### M6 — XorPairCombine cup-XOR motifs (module-local universal)
**3 decls, 3 motifs at counts {150, 82, 16} sites each**, all over
`{Bool.xor, Prod.fst, Prod.snd}`:
```
  fun p acc => Bool.xor (Prod.snd p) acc        -- 150 sites
  fun p acc => Bool.xor (Prod.fst p) acc        --  82 sites
  fun p acc => Bool.xor (Prod.fst p ⊕ Prod.snd p) acc  -- 16 sites
```
*Interpretation*: a single underlying lemma
`foldr_xor_proj : ∀ φ, List.foldr (λ p acc, Bool.xor (φ p) acc) false
                         ⇔ Bool.xor of (l.map φ)`
would subsume all three variants (with `φ ∈ {fst, snd, λp, fst p ⊕ snd p}`).
The high per-decl site count (≈ 80 sites per file) is `decide`
expansion, not duplicated reasoning — but the **algebraic content**
is exactly one linear-projection lemma.  **Abstraction candidate #5.**

### M7 — delta_zero ⊃ delta_add (shared lex-insertion fold)
**2 decls, 36 sites, ops = {`subsetIdx`, `kSubset`, `binom`,
`eraseIdx`, `Nat.decLt`, `LT.lt`}** —
`Cohomology.CupAW.Zero.delta_zero` and
`Cohomology.Delta.Linear.delta_add` share the lex-insertion fold.
*Interpretation*: `delta_zero` is the zero-case specialisation of
`delta_add`; they could be one theorem.

### M8 — Cauchy-Schwarz inductive crossSum / dotList / sumSqList
**4 decls, ops = {`HAdd`, `HMul`, `Nat.succ`, `Nat.below`,
`dotList.match_1`}** — shared `Nat.brecOn` skeleton across the
Cauchy-Schwarz inductive proof family.

### M9 — Euler-sequence bounds family
**3 decls, ops = {`HAdd`, `HMul`, `GE`, `eulerNum`, `eulerDen`}**:
`euler_upper_inv`, `euler_sharper_lower`, `euler_sharper_8_3_pure`
share the Euler-bound recursor skeleton.

### M10 — `HAdd + HMul` arithmetic induction baseline
**5 decls** including `Meta.Nat.PureNat.add_mul`,
`mul_assoc`, `ModArith.trichotomy`, `DyadicFSM.LCMClosure.bs_periodic`.
The fundamental Nat induction skeleton.

---

## Cross-cutting interpretations

### Algorithm / proof-structure hints

1. **Tiny vocabulary**: 5 recursor tags carry all 720 sites.  DRLT
   has algorithmically narrowed to "List reduction + Nat induction
   + decidable arithmetic".  Any new construction in this style
   should land in this vocabulary; anything that needs richer
   recursion (Fin folds, well-founded recursion) signals either a
   stylistic outlier or a new primitive to be justified.

2. **Pattern #2 universal quantified**: M3 (8 decls), M4 (4 decls),
   M5 (9 decls combined) all instantiate the same Pattern #2 shape
   from `LESSONS_LEARNED.md` — induction over a Nat parameter with
   decide-discharged base.  Total: at least 21 decls follow this
   exact skeleton.

3. **Module-local universals as the modal pattern**: Most strong
   clusters (M3, M4, M5, M6) live inside one tree (DyadicFSM, Sqrt,
   ModArith, XorPairCombine).  The codebase pattern is "develop a
   skeleton inside a sub-tree, instantiate per-parameter, do not
   abstract globally".  This is consistent with the *seq → pure*
   evolution noted in `LESSONS_LEARNED.md`.

### Math-content hints

1. **Σ-fold cross-domain (M2)**: physics observables and Gram inner
   products literally share the same `foldl + HAdd` skeleton.  Not
   just analogically — the elaborated `Expr` is identical post
   normalisation.  This is direct evidence that the math/physics
   distinction is sociological, not structural, at the fold level.

2. **XorPairCombine ↔ ℤ/2-bilinear form (M6)**: the three foldr-XOR
   variants `(fst, snd, fst⊕snd)` are exactly the three ℤ/2-linear
   projections of `(α, β) ∈ Bool × Bool`.  The fact that all three
   compile to the same fold skeleton (modulo which projection)
   confirms the foldr-XOR is realising a linear-projection algebra.
   General theorem hinted: `foldr_xor_proj : foldr (xor ∘ φ) false l
   = Bool.xor over (l.map φ)`.

3. **Irrationality is one theorem (M4)**: `√2`, `√3`, `√5`
   irrationality currently live in three separate files with three
   separate `_no_rational_aux` proofs whose elaborated recursors
   are byte-identical (in operator-multiset terms).  This screams
   `sqrtN_irrational : ∀ N, ¬IsPerfectSquare N → Irrational (√N)`
   should exist as one Lean theorem.  G87's clearest immediate
   action.

---

## Concrete next actions

**Abstraction candidates surfaced (priority order)**:

1. `sqrtN_no_rational_aux : ∀ N, ¬IsPerfectSquare N → ...`
   (subsume Sqrt2KernelFree/Sqrt2Pure/Sqrt3Pure/Sqrt5Pure)
2. `foldr_xor_proj : ∀ φ : Prod Bool Bool → Bool, ...`
   (subsume XorPairCombine triplet)
3. `sigmaList : (List α) → (α → ℕ) → ℕ` + Σ-fold lemmas
   (subsume Linalg/Physics observable sums)
4. `pellProperModN_period` parametric (subsume 8 modN decls)
5. `mod_p_classification` parametric (subsume mod3 / mod5 family)
6. `delta_add ⊃ delta_zero` consolidation

If any of these turn into PURE lemmas with strictly fewer total
PURE-count than today's hand-instantiated versions, the corpus
shrinks while coverage grows — that's the integration win.

**Tooling extensions worth considering**:

  * Lift `argIdx` per-tag — currently we use argIdx=2 across tags
    by coincidence; that breaks if `List.foldlM` etc start
    appearing (their step lives at a different index).
  * Add **Syntax-level** scan (Tier 1) for tactic-block patterns
    (`induction`/`rw`/`simp` co-occurrence) as a complement.
  * Add **proof-term DAG** depth analysis — does a fold appear in
    the *spine* of the proof or just in a sub-term?  Tells us
    whether the algebra is the load-bearing structure of the
    theorem or incidental.

---

## Artifact map

  * `tools/ast_fold_scan.py` — driver (Python)
  * `tools/ast_fold_scan_body.lean` — canonical Lean scanner body
  * `tools/_ast_fold_scan_last.log` — last raw build log (gitignored)
  * `tools/_ast_fold_scan_rows.tsv` — extracted TSV rows (gitignored)
  * `lean/E213/_AstFoldScanProbe.lean` — ephemeral probe
    (auto-deleted after successful run; gitignored)

Run `tools/ast_fold_scan.py` to re-execute the full pipeline,
`--report-only --loose` to re-cluster the existing rows.
