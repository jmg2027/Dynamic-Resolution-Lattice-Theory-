# Methodology patterns

Recurring proof techniques, refactor patterns, and methodology
insights surfaced while closing Lean sub-trees.  Each pattern is a
named, reusable reduction or strategy with concrete examples in
`lean/E213/`.

Distinct from `theory/math/pattern_catalog/pattern_catalog.md`,
which catalogues *formalised-in-Lean* proof patterns (the
`Lib/Math/PatternCatalog/` sub-tree).  This file catalogues
methodology — the *human-side* heuristics that guide closure work.

---

## Reduction patterns (2026-05-20)

**원칙**: 정리 숫자나 줄 수가 아니라 *내용 밀도와 가독성*이 목표.
많이 쌓이면 인지적 부하가 늘어나서 새 통찰이 안 나온다.  
"줄이라"는 무작정 삭제가 아니라 *방향성·가독성·통찰 친화도*를
높이는 작업.

### Smell #1: layer-by-layer enumeration

증상: `_layer0`, `_layer1`, ..., `_layerN` 형태의 정리 N개 +
선택적으로 `_bundle_Nlayer` 형태의 묶음.

원인: 일반 ∀-form이 증명 도구 부족 (e.g. `ring`/`linarith` 없음) 또는
미완성이라 layer-by-layer 검증으로 회피.

처리:
- 묶음만 남기고 개별 layer 삭제.
- 구조적 이유 (recurrence-uniqueness 등) 식별 → 별도 lemma로 추출.
- 예: `Mobius213.pell_recurrence_unique` — 2nd-order recurrence + 
  initial values 일치 ⟹ 두 sequence 일치.  16-conjunct bundle을
  단일 uniqueness lemma + recurrence/initial 확인으로 대체 가능.

### Smell #2: same-content reformulation across files

증상: `Lens/UndifferentiatedRaw.constLens_collapses`,
`Lens/RawTopology.indiscrete_kernel_total`,
`Lens/RawTopology.indiscrete_globally_collapsed` — 모두 같은 사실
"`(constLens e).view r = (constLens e).view s` for all r, s"의 
다른 표현 (view 형 / kernel 형 / globally-collapsed 형).

처리: 한 파일에 통합, canonical name 하나 + 필요시 view↔equiv 형
대응 lemma 1개.  Triple-redundancy → 2개로 축소.

### Smell #3: incremental scaffold theorems

증상: 마스터 정리에 도달하기 위한 단일 등식 검증 정리들
(`gap_e7_eq_5443`, `pi5_gap_e7_eq_5446`, `..._distance_eq_3`)이
모두 마스터의 conjunct로 그대로 들어 있음.

처리: 외부에서 직접 참조되지 않는 incremental은 삭제.  
마스터의 conjunct로 충분.  외부 caller 있는 incremental만 유지.

### Smell #4: cluster + atomic + bundle 패턴의 중복

증상: 한 파일에 atomic_a, atomic_b 정리 + atomic_bundle (= atomic_a
∧ atomic_b) + slash 정리 + full_bundle (= atomic_a ∧ atomic_b ∧
slash).  atomic_bundle은 full_bundle의 부분 형식.

처리: 미세한 redundancy.  파일 narrative가 atomic vs slash 구별을
교육적으로 강조한다면 둘 다 유지 가능.  단순 alias라면 atomic_bundle
삭제.  `Lens/SelfCompletion`은 narrative 가치로 6개 유지함.

### 적용 결과 (2026-05-20)

session-added 파일들에 적용:
- Mobius213: 21 → 13 (8개 layer 삭제 + 2개 structural insight 추가)
- FibonacciExtended: 16 → 9 (개별 F_N 5개 삭제, bridge 16-conjunct 1개로 통합)
- PiFiveGap: 20 → 14 (incremental 6개 삭제)
- PureAtomicObservables: 17 → 14 conjuncts (중복 3개 제거 + 구조별 grouping)
- RawTopology+UndifferentiatedRaw: 12 → 7 + 파일 1개 통합 삭제

순 reduction: 86 → 57 theorems, ~500줄, 파일 1개.  
*같은 수학적 content, 더 적은 cognitive surface*.

---

## Reduction patterns (2026-05-20, expanded after lean/-tree sweep)

After the second sweep (lean/ tree, 4 parallel audit agents +
~10 hand-applied reductions), the pattern catalog is enriched
with new sub-patterns and explicit caveats about agent over-flagging.

### Smell #1 refinement — truth-table singletons

Specific instance of #1: four `_TT/_TF/_FT/_FF` rfl theorems
(or 8 for two operations).  Collapse to one ∧-bundled
"truth_table" theorem proved by `<;> (unfold; decide)`.

Examples cleaned: `Lens/Bool213/Raw` (and/or 8 → 2),
`Lens/Compose/OnLensImage` (declined — used as proof
components downstream).

### Smell #5: biconditional split into 3 theorems

A new pattern not in the original list: a biconditional iff
stated as three theorems — forward direction, reverse direction,
and the iff itself.  Each direction's proof is small; the iff's
proof is just `⟨reverse, forward⟩`.

Reduction: keep ONLY the iff, with both proof directions inlined
(`refine ⟨intro h; ..., intro h; ...⟩`).  Saves 2 theorems and
the redundant docstrings.

Example cleaned: `Lens/Bool213/Raw.booleanProj_id_iff_isBool213`.

### Smell #6: per-parameter applications of a meta-algorithm

A generic meta-theorem parameterised by `(a, b, j, N₀)` followed
by 4-6 individual applications (`thm_8_3`, `thm_10_4`, ...).
Each is a single call to the meta with concrete arguments.

Reduction: drop the per-parameter applications.  Callers
instantiate the meta inline (`euler_lower_generic 8 3 4 (by
decide) (by decide)`).  Saves 4-6 theorems per such cluster.

Example cleaned: `Cauchy/Euler` (e_gt_8_3, e_gt_10_4, etc., 6
theorems dropped).

### Agent-over-flagging caveat

About **30%** of agent-flagged reductions turn out to be:

  · **External API points**: referenced by other files via `open`
    + named reference.  Always `grep` for external use before
    deletion.  Example: `Lens/Compose/OnLens.lensXor_comm_eqPW`
    looks redundant with `lensXor_comm` but is the canonical
    cutEq form referenced downstream.
  · **Proof components**: used by a "master" theorem in the
    same file via explicit name reference (not by `rfl` /
    `decide`).  Deleting breaks the master's proof. Example:
    `Compose/OnLensImage.lensXor_TT/_TF/_FT/_FF` are used by
    `boolToConstLens_xor`.
  · **Pedagogical demos**: files explicitly named `Demo.lean` or
    similar carry intentional narrative.  Example:
    `Theory/Raw/Demo.lean` depth_a/b/ab/aab/bab enumeration is
    pedagogical, not a true layer-by-layer enumeration.
  · **External witness capstones**: per-prime/per-instance
    theorems referenced by an aggregate bundle in another file.
    Example: `DyadicFSM/Pell/ProperMod.pellProper{N}_bits_period_K`
    are all referenced from `Pell/Proper8.lean`.

**Process**: after agent reports candidates, always verify:
  1. `grep -rn "<theorem_name>" lean/E213 | grep -v <own_file>`
  2. Check whether the file is `Demo.lean` / `Examples.lean`
  3. Open the file, check whether the theorem is referenced
     elsewhere in the same file (proof component).

### Hand-applied this session

| File | Reduction | Net |
|------|-----------|-----|
| Symmetry/AutKChiral | dropped 13 internal scaffolds | ~50 lines |
| Atomic/Hydrogen | dropped 4 scaffolds | 12 lines |
| Atomic/Helium | dropped 4 scaffolds | 15 lines |
| AlphaEM/ChannelCohomologyLoss | bundled 5 minor theorems | 10 lines |
| Math/Combinatorics/Binomial | 10 → 2 (bundled rows) | 25 lines |
| Lens/Cardinality/Tower | 6 layer rungs → 1 unbounded | 22 lines |
| Lens/SyntacticInternalization | dropped 5 rfl | 8 lines |
| Meta/LensInternality | dropped 3 rfl | 10 lines |
| Symmetry/GluonChannelInterpretation | dropped 2 trivial | 14 lines |
| Cohomology/Surfaces/T2Squared/HodgeIndex | 6 diag → 1 bundle | 7 lines |
| AlphaEM/LaplacianSpectrum | dropped 13 scaffolds | 28 lines |
| Mass/TauOverMu | 6 scaffolds → master conjuncts | 35 lines |
| Lens/Bool213/Raw | 8 truth tables → 2 bundles + iff merge | 30 lines |
| Cauchy/Euler | dropped 6 per-param applications | 25 lines |
| Lens/Cardinality/LensCardinality | 4 witnesses → 1 bundle | 5 lines |

Net: ~85 theorems removed across 15 files, ~300 lines off, build
clean throughout, ∅-axiom contract preserved.

### Patterns DEFERRED (require deeper refactor)

  · `DyadicFSM/Pell/ProperMod` (per-prime enumeration): generic
    `pellProperFSMmod_period_invariant` lemma would replace 10
    theorems, but each proof needs a `decide` base step at the
    specific (prime, period) — non-trivial to abstract.
  · `DyadicFSM/Pisano/Predictor{6,7,8,11,...}` (8 per-base
    files): consolidation into 1 master capstone is high-impact
    but high-risk (cross-file API changes).
  · `CayleyDickson/Integer` (15 files with parallel projection
    lemmas): typeclass refactor (`GaussianLike`) would save 14
    lemmas × 15 files = 210 statements; substantial Lean-design
    work, not within this session's scope.
  · `PureNatMod3/5` (mod-p descent templates): generic
    `mod_p_descent_template` parameterised by `(p : Nat) [Prime
    p]` would save ~18 theorems; requires careful prime
    abstraction.

These remain as **research directions** rather than mechanical
cleanups — each needs structural thinking similar to the
`pell_recurrence_unique` extraction from Mobius213.

---

## Hero-session methodological patterns (2026-05-21)

Patterns surfaced during the Phase 1 hero target push (Möbius
213-tower L_∞).  These are not domain-specific; they apply
whenever 213-native PURE statements meet limitations of Lean 4
core (no Mathlib).

### Pattern #1: 213-native Int polynomial identity via Int213.* rw chain

**Problem**: Mathlib's `ring` tactic is forbidden.  `simp only` +
`omega` works for many Int identities but introduces [propext,
Quot.sound] kernel-axiom dependency — kernel-allowed but not
strict PURE.

**Solution**: replace `simp + omega` with a manual `rw` chain
using only `E213.Meta.Int213.*` lemmas.  PURE.

**7-step canonical sequence** (proved on `cross_step_algebra` at
`Mobius213.lean ~226`):

```
1. `(-1) * x → -x`        via Int213.neg_mul + Int.one_mul
2. Drop `+ 0` summands     via Int.add_zero
3. Distribute              via Int213.mul_add, Int213.add_mul
4. Pull negatives          via Int213.mul_neg, Int213.neg_mul
5. Normalise associativity via Int213.mul_left_comm + Int213.mul_assoc
6. Cancel matching pairs   via Int213.add_assoc + add_left_comm + add_neg_cancel
7. Sign cleanup            via Int213.add_comm + Int.sub_eq_add_neg
```

**When to use**: any moderate-degree (quadratic / cubic in the
unknown variables) polynomial identity over Int.  The chain
is ~25-30 lines but mechanical — each step has a single named
lemma — and yields strict PURE.

**Reusable target**: many of the ~50 real-DIRTY theorems in
`STRICT_ZERO_AXIOM.md` that use `omega` shortcut after `simp` can
likely be PURE-refactored with this pattern.  Identify by
`grep -B 5 omega lean/ | grep simp` and applying the chain.

**Anti-pattern**: do NOT use `ring`, `ring_nf`, `linarith`,
`field_simp` — all Mathlib.  Do NOT use `set` (Mathlib tactic);
work directly on the long expressions or use `let` in term mode.

### Pattern #2: Decide-by-Bool-tuple parameterisation

**Problem**: Lean 4 core (without Mathlib) does NOT synthesise
`Decidable (∀ f : Fin n → Bool, P f)` from `Fintype` instances.
Even `Fintype (Fin 5 → Bool)` doesn't get a usable
`decidableForallFintype`.  Direct `∀ α : Fin n → Bool, … := by
decide` fails with "failed to synthesise Decidable".

**Solution**: parameterise the universal quantification by the
function's pointwise Bool values.  Lift via an explicit
`mkFn (b0 b1 … b_{n-1} : Bool) : Fin n → Bool := fun i =>
  if i.val = 0 then b0 else if i.val = 1 then b1 else …`

Then `∀ (b0 … b_{n-1} : Bool) (extra args), P (mkFn b0 … b_{n-1})
:= by decide` works — Lean enumerates 2^n cases on the Bool tuple.

**Logical equivalence**: this universal-over-tuple form is
equivalent to the universal-over-function form by function
extensionality on `Fin n → Bool`, which is `rfl` elementwise.

**When to use**: any combinatorial statement quantified over a
finite function space (cochains, characters, indicator vectors)
that you want to prove by exhaustive enumeration.

**Caveat (Phase 2 finding)**: this pattern *also exposed a bug*
in `Cohomology/Cup/Core.lean` — see "Pattern #5" below.  The
finer the decide-enumeration, the more likely you surface
implementation issues that 4 hand-picked concrete cases missed.

### Pattern #3: Docstring `-/` trap

**Problem**: Lean 4's docstring delimiter is `/-! … -/` (or
`/-- … -/`).  Any `-/` substring inside the docstring closes it
prematurely, producing inscrutable "unexpected identifier" or
"unexpected token '*'" errors at the line where the FALSE close
ends.

**Trap text examples observed this session**:
  · `even-/odd-indexed Fibonacci numbers`  ← `-/` after "even"
  · `delta sign-/ordering convention`       ← `-/` after "sign"

**Solution**: avoid hyphen-immediately-followed-by-slash in
docstring prose.  Replace with `and`, ` and `, `, ` etc.:
  · `even- and odd-indexed Fibonacci`
  · `delta sign and ordering convention`

**Diagnostic hint**: when build fails with "unexpected token"
errors *far below* the actual problem line, search for `-/` in
preceding prose first.

### Pattern #4: Catalog misclaim self-correction

**Problem**: prior-session HANDOFF.md / catalog files advertise
a file at path X with theorem names {A, B, C}, but the actual
file tree has no such file — the content was merged into a
neighbouring file or never made it to commit.  Silent staleness.

**This session's instance** (commit 7a3e6e6e):
  · `catalogs/math-theorems.md §J.3` advertised
    `Lens/UndifferentiatedRaw.lean` with `constLens_collapses`,
    `pre_lens_singleton`, `constLens_kernel_total`.
  · `git log --diff-filter=A -- "**/UndifferentiatedRaw.lean"`
    returned empty — file never existed in git history.
  · Actual content lives in `Lens/RawTopology.lean` as
    `constLens_view_eq`, `k_infty_at_raw_bundle`, etc.

**Solution direction** (per CLAUDE.md §8): "fix the claim,
not the file."  If the catalog advertises X but reality is Y,
update the catalog to advertise Y at its current path with
current theorem names.  Do NOT recreate the phantom file unless
the original session-snapshot really intended it.

**Detection heuristic**: in `ready-to-merge` audit, extract every
`import E213.<module>` from catalog files and verify the
corresponding `lean/E213/<module>.lean` exists.  Mismatches =
misclaims to correct.  Script:
```
grep -rh "import E213\." catalogs/ books/ blueprints/ \
  | sed -E 's/.*import (E213\.[A-Za-z0-9_.]+).*/\1/' \
  | sort -u \
  | while IFS= read -r imp; do
      path=$(echo "$imp" | sed 's|E213\.|lean/E213/|; s|\.|/|g').lean
      test -f "$path" || echo "MISCLAIM: $imp"
    done
```

**Counter-example (legitimate stale)**: when 100+ imports point at
a moved subtree (e.g., Real213/* → Analysis/*), the catalog is
"systematically stale" rather than misclaiming — fix with a top-of-
file reorg note + umbrella import (Path A) or full rewrite (Path B,
deferred).

### Pattern #5: Decide as bug-finder for "universal claim"

**Problem**: standard mathematical results (cup-product Leibniz,
graded-ring identities, etc.) are often *asserted* as universal
in the code's docstrings but the actual `def` may diverge from
the standard convention.  Hand-picked concrete tests using
highly-symmetric inputs miss the divergence.

**This session's instance** (Phase 2):
  · `Cup/Core.lean` docstring: "Cup product (Alexander–Whitney)"
  · `Cup/Core.lean` implementation: `(α ⌣ β)(τ) = α(τ.take k) ·
    β(τ.drop k)` — this is the **concatenation cup**, not AW
    (AW has shared vertex at τ[k], so front has `k+1` elements).
  · Existing `Cup/Leibniz.lean` proves Leibniz at 4 concrete
    pairs (all symmetric: v0, all_true, zero).  All pass.
  · Pattern #2 parameterised Leibniz over `Bool^{10}` (all
    1024 cochain pairs at bidegree (1,1)) — `decide` reports
    **false**.
  · Manual eval pinpoints counterexample: `basis₀ ⌣ basis₂` at
    face `[0, 1, 2]` gives LHS = true, RHS = false.

**Pattern (the general one)**: when adding a universal claim
that "everyone knows" holds, *force decide-level enumeration*
via Pattern #2.  If decide refutes, you've found either:
  (a) an implementation divergence from the standard convention
      (docstring claims X, code implements Y), OR
  (b) a sign / ordering / index off-by-one in a supporting def
      (in Phase 2: cup's no-shared-vertex convention requires a
      twisted Leibniz, not the standard one).

**Why this matters strategically**: 213's "no Mathlib, all
hand-rolled" approach means *every* foundational def is
hand-written and could deviate from the literature.  Standard
identities being mechanically *checked* (not just stated) is
the only protection against silent drift.  The Pattern #2 +
Pattern #5 combo (parameterise → decide) is the cheap insurance.

**Action for next session**: replicate Pattern #5 across other
"obvious" universal claims in `Cohomology/`, `HodgeConjecture/`,
`Linalg213/`.  Each parameterisation is ~20 lines but can surface
unknown drift.

---

## Cumulative pattern summary (post-2026-05-21)

| Pattern | Domain | Reusability |
|---|---|---|
| #1 Int213 rw chain | strict-PURE polynomial identities | high — applicable to ~50 DIRTY budget |
| #2 Bool-tuple parameterise | finite-function-space ∀-claims | high — Lean-core limitation workaround |
| #3 docstring `-/` trap | doc-writing hygiene | universal |
| #4 catalog misclaim correction | ready-to-merge audits | universal |
| #5 decide as bug-finder | universal-claim verification | high — defends against silent drift |
| #6 list-level decoupling | bypassing Fin/colex indexing for symbolic proofs | high |
| #7 3-way partition (face-removal) | δ XOR sum decomposition at boundary | high — general cohomology |

These compose: #2 enables #5 (enumeration), #5 surfaces bugs that
hand-tests miss, #1 fixes the [propext] residue that often
remains after #5's enumeration approach.  #6 + #7 enable
*symbolic* proofs that don't need decide enumeration at all.

---

## Pattern #6: List-level decoupling for symbolic proofs

**Problem**: cup/delta operations in `Cohomology/` use
`Fin (binom n k)` indexing with `subsetIdx` colex lookups.  This
makes universal-form proofs at general (n, k, l) require
`subsetIdx ↔ kSubset` round-trip lemmas (substantial structural
work).  Yet the *algebraic content* of the theorem doesn't need
the Fin indexing — it's about take/drop/eraseIdx on lists.

**Solution**: define list-level analogs `cupList`, `deltaList`
that take `α β : List Nat → Bool` and `τ : List Nat` directly.
Prove the theorem at this level.  Transfer back to Fin-indexed
form via the round-trip lemmas (out of scope for the symbolic
result itself).

Pioneer demonstration: `Cohomology/Cup/LeibnizLexListLevel.lean`
proves the (1, 1) AND (2, 1) twisted Leibniz at the list level
without any decide enumeration — just structural lemmas + Bool
case analysis on (k+l+2) atoms.

**When to apply**: any theorem about Fin-indexed operations whose
algebraic content is "shape-preserving" (take/drop/eraseIdx on
sequences) — define a List-level abstraction, prove there, transfer.

---

## Pattern #7: 3-way partition strategy — CLOSED at ∀(k,l) (2026-05-22)

**Problem**: at the cochain level, `δ(α ⌣ β)(τ)` is a foldl-XOR
sum over face removals.  Standard Leibniz captures faces at
"endpoint" positions but may miss "interior" positions (per
G85/G86's lex-projection cup finding).

**Solution** (user's 3-way partition strategy):
- Partition the foldl XOR over `[0..k+l]` at position k into:
  - Block 1: i ∈ [0..k-1]  →  corresponds to (δα ⌣ β)(τ)
  - Block 2: i = k          →  the missing-face *correction*
  - Block 3: i ∈ [k+1..k+l] →  corresponds to (α ⌣ δβ)(τ)
- Apply take/drop ↔ eraseIdx commutation lemmas at each i
- (δα ⌣ β) covers Blocks 1 + 2 (overlap with Block 2 at i=k)
- (α ⌣ δβ) covers Blocks 2 + 3 (overlap with Block 2 at j=0)
- Block 2 appears TWICE in RHS → XOR-cancels in ℤ/2
- Net: LHS = (δα⌣β) ⊕ (α⌣δβ) ⊕ Block 2 = standard RHS ⊕ correction

**Concrete realisation**: `Cohomology/Cup/LeibnizLexStructural.lean`
(8 PURE structural lemmas covering all three i-cases) plus
`Cohomology/Cup/LeibnizLexListLevel.lean` (foldl XOR algebra + the
3-way assembly at (1,1) and (2,1) bidegrees).

**Generalisation**: same strategy applies to other "boundary
self-correcting" operations in cohomology — cap product, twisted
ring operations, K_{m,n}^{(c)} bipartite cup channels.  The
**self-referential Leibniz** (correction = operation at face)
is structurally similar across these contexts.

**Closure status** (2026-05-22): the ∀(k,l) symbolic twisted
Leibniz is PROVED PURE at the list level in
`Cohomology/Cup/LeibnizLexListLevel.list_level_leibniz_general`.
Required additional infrastructure beyond Pattern #7's structural
lemmas:

  · Custom `xorRange : Nat → (Nat → Bool) → Bool` (avoids
    List.range_succ which is [propext]).
  · `xorRange_split` — at position k decomposes xorRange (k+l+1)
    into three blocks.  Pure structural induction on l.
  · `xorRange_three_way_partition` — abstract algebraic skeleton
    composing xorRange_split with xorRange_congr.  PURE.
  · `cupList_face_decomp` — discharges the three hypotheses of
    xorRange_three_way_partition for the cup operation.
  · `list_level_LHS_partition` — LHS in explicit 3-block form.
  · XOR algebra closures (and_xor_distrib_left/right,
    and_distrib_xorRange_left/right, xor_self', xor_false_right,
    xor_assoc') reducing to 4-atom Bool case analysis.

Total: 32 PURE theorems across `LeibnizLexStructural.lean` (8) and
`LeibnizLexListLevel.lean` (24).  No Mathlib, no funext, no decide
enumeration over the (α, β) parameter space.

---

## Pattern #8 — `Int.NonNeg` constructor inversion bypasses Int-ordering propext

**Discovered**: 2026-05-22 session 2 (6-theorem marathon, Diophantine
completeness sub-task).

### Problem

Lean-core Int ordering lemmas (`Int.le_trans`, `Int.lt_of_lt_of_le`,
`Int.ofNat_le`, `Int.not_lt`, `Int.add_le_add`, `Nat.sub_lt_sub_right`,
`Nat.add_sub_cancel`, etc.) all carry `propext` in their axiom
dependency.  The Iff form `Int.ofNat_le : Int.ofNat a ≤ Int.ofNat b
↔ a ≤ b` is the most common offender.  Likewise `omega`,
`Bool.and_eq_true`, and several `Nat.*` ordering helpers.

This blocks Int-side diophantine / bounded-square reasoning from
being PURE.

### Solution: direct `Int.NonNeg` constructor matching

`Int.le a b := Int.NonNeg (b - a)` definitionally (`Init/Data/Int/Basic.lean`
line 174).  `Int.NonNeg` is a single-constructor inductive Prop:

```
inductive Int.NonNeg : Int → Prop
  | mk : ∀ (n : Nat), Int.NonNeg (Int.ofNat n)
```

When `b - a` reduces to `Int.negSucc k` (i.e., negative), the only
inhabitant `Int.NonNeg.mk n` would require `Int.ofNat n = Int.negSucc k`
— impossible by constructor injection.  `cases h` (on `h : a ≤ b`)
**automatically detects this** and closes the goal with no further
tactic.

### Concrete idiom

```lean
-- Bypass Int.ofNat_le.mp (propext) for the n ≥ 2 contradiction
private theorem ofNat_int_le_one (n : Nat) (h : (Int.ofNat n : Int) ≤ 1) :
    n = 0 ∨ n = 1 := by
  match n with
  | 0 => left; rfl
  | 1 => right; rfl
  | k+2 =>
    exfalso
    cases h    -- ★ Int.NonNeg (1 - ofNat (k+2)) is on negSucc — cases impossible
```

### Where applied

  · `ZOmegaUnits.lean §5` — `int_sq_le_one : x * x ≤ 1 → x ∈ {-1, 0, 1}`
    PURE via `ofNat_int_le_one` helper.
  · `KSubsetStructural.lean §0` — `nat_sub_lt_sub_right`,
    `nat_add_sub_cancel` PURE replacements for Lean-core propext-tainted
    versions, via Nat induction + the same NonNeg principle.
  · `FinBridgeGeneral.lean §0` — `take_append_le`, `drop_append_le`,
    `take_of_length_le`, `drop_of_length_le` PURE replacements for
    `List.take_append_of_le_length` etc.

### When NOT to apply

Symbolic Int algebra (`ring`, `ring_nf`) is still propext-tainted and
has no `Int.NonNeg`-style bypass.  Multi-variable polynomial identities
must be expanded manually via `Int213` axioms.  See Pattern #10
candidate (4·normSq ring identity, ~50 manual rewrites, currently
deferred).

### Scope refinement (mechanical audit)

A whole-Lib/ scan for `omega`-as-the-only-DIRTY-source surfaces a
much smaller refactor candidate set than initially expected.  Two
constraints narrow the field:

  · **omega is rarely the *sole* propext source.**  In the densest
    cluster found (`CayleyDickson/Integer/ZOmegaDomain.lean`, 8
    omega usages across 4 DIRTY theorems), the [propext, Quot.sound]
    tags also flow through `Int.mul_eq_zero`, `Int.sub_mul`,
    `Int.mul_neg`, and other Int-core rewrites used by the `simp
    only [...]` chains.  Replacing the trailing `omega` alone leaves
    the theorem DIRTY.
  · **Pattern #8 fixes ordering, not polynomial identity.**  Most
    omega usages in Lib/ close *symbolic* identities ("after these
    rewrites, the LHS equals the RHS"), not *ordering* claims.
    Pattern #8 has no `Int.NonNeg`-style bypass for the former (see
    "When NOT to apply" above).

The realistic Pattern #8 yield in Lib/ is **single-digit**, not the
~50 originally estimated.  The denser refactor strategy must combine
Pattern #8 with a separate Int-rewrite-replacement (analogue of the
`Int213` axiom set lifted to Lib/) — multi-session work, not a
one-pass mechanical sweep.

Open candidates (verified):

  · `CayleyDickson/Integer/ZOmegaDomain.lean`: 4 DIRTY theorems
    (`normSq_mul`, `conj_mul`, `normSq_nonneg`, `normSq_eq_zero_iff`)
    blocked by Int-rewrite propext, not omega.
  · `CayleyDickson/Levels/CayleyHeavy.lean`: similar shape on
    `lip_normSq_nonneg` etc.
  · `Choice/CanonicalTruthChar.lean`: 1 omega in helper
    `slash_ne_b_via_depth`, but downstream DIRTY items derive from
    iff/propext, not the helper.

These remain Open Frontier for a dedicated session that pairs
Pattern #8 with a Lib/-side Int-rewrite extension.

---

## Pattern #9 — Clause-4 recursive Lens application closes postulate gaps

**Discovered**: 2026-05-22 session 2 (alive gap closure, G87 §11).

### Problem

The atomicity proof's `IsAlive` predicate (both decomposition parts
have odd parity) was historically **postulated, not derived from Raw**
— "the exterior-algebra / fermion-statistics pattern, natural partner
to Raw's binary structure but postulated" (`Atomicity/Alive.lean`
pre-2026-05-22 docstring).  This was identified as the single largest
gap in the Raw → 5 inevitability chain (G87 §2.2).

### Solution: Clause 4 applies recursively at every granularity

User insight (2026-05-22):
  > "Raw는 트리 형태가 아니다.  모든 Raw는 연산이기도 하고 객체이기도
  >  하기 때문 — 즉 애초에 연산과 객체도 정의되지 않은 상태이다."

If every Raw event is simultaneously operation and object — with no
a-priori distinction — then Clause 4 of the 213 axiom (`x/x` forbidden,
`seed/AXIOM/02_axiom.md` §2.2 #4) is **not restricted to atomic
Raw distinguishables**.  It applies at every granularity, including
groups of Raw viewed as objects.

For decomposition `n = 2a + 3b`: if `a` is even, the `a` binary-pair
atoms can themselves be grouped into `a/2` pair-of-pairs — a Clause-4
violation at the binary group level.  So `a` must be odd; similarly `b`.

### Concrete dissolution

```lean
def IsSelfPaired (n : Nat) : Prop := ∃ k, n = 2 * k
def IsClause4Alive (a b : Nat) : Prop := ¬IsSelfPaired a ∧ ¬IsSelfPaired b

theorem alive_iff_clause4_alive (a b : Nat) :
    IsAlive a b ↔ IsClause4Alive a b
```

The "both odd" alive predicate is the **count-Lens readout of Clause 4
applied recursively** — not a separate postulate.  Lean witnesses in
`Theory/Atomicity/AliveDerivation.lean` (7 PURE).

### Generalisation

Any apparently-postulated structural predicate `P` in 213-Algebra
should be reconsidered through the lens: **does `P` correspond to
Clause-4 (or another axiom clause) applied at a non-atomic
granularity?**  The user's "all Raw are simultaneously operation and
object" principle authorises recursive application of any 4-clause
content to count-Lens groups, type objects, group objects, etc.

### Where applied (so far)

  · `AliveDerivation.lean` — `IsAlive` ↔ recursive Clause 4 on
    NT-pairs and NS-triples (`alive_iff_clause4_alive`, 7 PURE).
  · `Cohomology/NodupAsClause4.lean` — `List.Nodup` ↔ recursive
    Clause 4 at the list-index level (`nodup_iff_clause4Nodup`,
    12 PURE).  A list has no duplicates iff no two distinct
    index positions are paired with the same element — the
    no-self-pair axiom read at list granularity.

### Future candidates

  · "Sortedness" postulates in colex enumeration — Clause 1
    (distinguishing) applied recursively, giving canonical order.

---

## Pattern #10 — Adoption-gap detection via k-gram cascade scan (2026-05-22)

**Source**: G99 (k-gram cascade scanner) → N8/N9 batch execution this
session.

**Statement**: When a PURE helper lemma already exists in the codebase
but the corpus shadows it via manual 2-3 step `rw` chains, the gap
surfaces as a high-frequency k-gram in tactic-token scans.  Adopt the
helper mechanically; the corpus shrinks without any new mathematics.

**Witness** (this session):

  · `NatHelper.mul_left_comm` (already PURE) ↔ 19 sites doing manual
    `[← mul_assoc, mul_comm, mul_assoc]` 3-step.
    Adopted across 3 files (CutSumOne ×16, CutMidSelf ×2, Euler ×3);
    helper went from "cited once" to "cited 20+ times".
  · `Nat.add_right_comm` (Lean-core PURE) ↔ 6 sites doing manual
    `[add_assoc, add_comm, ← add_assoc]` 3-step.
    Adopted across 7 files; one site (LeibnizLexListLevel) collapsed
    to plain `rfl` once redundancy was stripped.

**Diagnostic step**: `tools/syntax_rw_cascade_scan.py` (G99) ranks
adjacent `rw` k-grams by frequency.  Top entries that aren't already
named lemmas are adoption candidates.

**Mechanical execution**: term-mode replacement
(`exact NatHelper.mul_left_comm a b c`) where the goal is exactly the
helper's RHS; tactic-mode (`rw [NatHelper.mul_left_comm]`) where
the helper appears inside a longer chain.

**Failure mode this catches**: lemma rot — a helper is added once,
then forgotten as subsequent contributors reach for the underlying
3-step rewrite without checking whether a wrapper exists.  The k-gram
scan is the periodic-audit antidote.

---

## Pattern #11 — Pointwise dichotomy collapse for Cup-Leibniz lifts (2026-05-22)

**Source**: G91 / G94 §8.1 L2 → execution this session
(`LeibnizDecomp.lean`).

**Statement**: When a basis-component family `bz5_X β k j` has the
two-case pointwise shape

```
β k = false  →  ∀ j, bz5_X β k j = Cochain.zero _ _ j
β k = true   →  ∀ j, bz5_X β k j = basis _ _ k j
```

Cup-AW Leibniz for the family decomposes into two reusable lemmas:

  (a) **Zero collapse** — when `γ ≡ 0`, all three Leibniz terms
      collapse to `false` via `cupAW_zero_left/right` + `delta_zero`,
      and the identity reduces to `false = xor false false` (rfl).
  (b) **Pointwise transport** — when `γ ≡ basis`, both sides rewrite
      via `cupAW_pointwise_eq` + `delta_pointwise_eq` and the identity
      reduces to the basis Leibniz at the basis element.

The two helpers (one per side: `left` decomposes first cochain, `right`
decomposes second) cover the 4 sibling `h_components_{α,β}` proofs in
`Leibniz{21,22}Final.lean`.

**Witness**: `Lib/Math/Cohomology/CupAW/LeibnizDecomp.lean` — 8 PURE
helpers (4 zero-collapse + 4 pointwise-transport, specialised to
right-degree b ∈ {1, 2} since `2 + b - 1 + 1` does not reduce
definitionally for abstract `b`).

  · Refactor result: 4 sites × ~30-line dichotomy → 4 sites × 6-line
    `cases` + 2 helper invocations.
  · Net: 147 lines removed, all `h_components_{α,β}` and
    downstream `leibniz_universal_5_2_{1,2}` remain PURE.

**Why specialised, not general**: a fully `(n, a, b)`-generic form
needs type casts to handle `(a+1)+b-1 ≢ a+b` defeq.  At the cost of
verbosity, specialising to the two actually-used (b=1, b=2) cases
keeps Fin indices identity-on-the-nose and avoids `Fin.cast`
plumbing.

---

## Pattern #12 — Meta-scan archetype catalog (2026-05-22)

**Source**: G101 §6 + G107 §6 tool inventory.

**Statement**: When the corpus needs static-analysis investigation,
pick a scanner from the 6 established archetypes rather than
inventing a one-off scan.  Each archetype answers a different
question; together they triangulate.

**The 6 archetypes**:

| # | Archetype | Question answered | Reference tools |
|---|-----------|-------------------|-----------------|
| 1 | **AST motif scan** | Which fold/recursor primitives are used and where? | `tools/ast_fold_scan.py` (G90) |
| 2 | **Syntax skeleton scan** | Which tactic-token sequences repeat? | `tools/syntax_tactic_scan.py` (G91) |
| 3 | **Citation graph** | Who depends on whom at the lemma surface? | `tools/syntax_arg_scan.py` (G92) |
| 4 | **Context dumper** | What surrounds each cite of a key lemma? | `tools/syntax_arg_scan.py --context-target` (G94, G96) |
| 5 | **Co-occurrence chunk** | Which tactic sub-sequences cluster together? | `tools/syntax_unfold_scan.py` (G98) |
| 6 | **k-gram cascade** | Which manual sub-rewrites shadow existing helpers? | `tools/syntax_rw_cascade_scan.py` (G99, Pattern #10) |

Plus two Expr-level scanners:

| 7 | **Expr-level call graph** | Same as #3 but at elaboration layer | `tools/ast_callgraph_scan.py` (G102) |
| 8 | **Expr-shape density** | What's the proof-shape fingerprint per namespace? | `tools/ast_shape_scan.py` (G103) |

**Usage rule**: before writing a new scanner, check if one of the
8 covers the question.  If yes, run it (TSV is gitignored;
regenerate on demand).  If no, write a new one and add it to the
archetype list.

**Status**: SURFACED; CL-1 of G107 §10.5.

---

## Pattern #13 — Process model: meta surfaces, substantive executes (2026-05-22)

**Source**: G97 §6 + G107 §0 (cross-branch handshake documentation).

**Statement**: For static-analysis-heavy tasks, run two branches in
parallel:

  · **meta branch** — pattern surfacing, scanner tooling, research
    notes.  No PURE theorems added on this side; analysis only.
  · **substantive branch** — PURE theorem additions, abstraction
    execution, math marathons.

The two branches communicate via numbered research-notes
(`research-notes/G##*.md`) acting as handshake documents.  Each
handshake doc references the G-IDs it consumes / produces.

**Witness**: G93 → G96 → G94 → G97 handshake loop closed across
this pattern.  The substantive branch (PR #90) closed 6 meta-surfaced
items in cycle (C1 / C2 / C3 / C5 / N5 / N6).

**This branch's adoption**: G107's open registry was the executor
entry-point for the `claude/handoff-part-3-marathon-0XWmn` branch's
sweep, which closed:

  · §2: L2 + N7 + N8 + N9 + Sub-2 (5 of 5 mechanical-immediate).
  · §3: L1 β-side (2 of 4 L1 siblings) + C deferred.
  · §4: M + Pell-FSM (full sweep) + ModArith (3 of 8).

49 Pell-FSM family sites + 12 mathematical sites + 25 mechanical
adoptions = 86 sites absorbed via 18 PURE helpers.

**Rule for future cycles**: if the next investigation is
static-analysis-heavy and likely to surface many candidate items,
spin up a meta branch.  Otherwise stay on one branch.

**Status**: VALIDATED across one full cycle; CL-2 of G107 §10.5.

---

## Pattern composition update

The original 7 patterns (Cup-Leibniz session 1) + Pattern #8 (Int.NonNeg
bypass, session 2) + Pattern #9 (Clause-4 recursive Lens) + Pattern #10
(adoption-gap k-gram) + Pattern #11 (Cup-Leibniz dichotomy collapse)
+ Pattern #12 (meta-scan archetypes) + Pattern #13 (cross-branch
process model) form the 2026-05-22 composition table.  Patterns
#14-#20 (this commit) extend the table with meta-scan branch
findings: n-layer agreement, three-level Raw-derivation
(→ seed/THEOREM_METHODOLOGY_SUITE.md §TH-2), decide-finitism
(→ seed/THEOREM_METHODOLOGY_SUITE.md §TH-3), framework-internal
subsumption, byte-identical Expr cross-domain bridges,
forward/backward factor-knob, multiple Lens choices.  Together
they enable the closure of the Raw → (3, 2, 5) inevitability
chain at full ∅-axiom level + a validated meta-substantive
cross-branch workflow.


---

## Pattern #14 — Triple-layer (n-layer) agreement = abstraction inevitability

**Discovered**: 2026-05-21 meta-analysis (G91 L1 + G94 §1 +
G103 §3 + G106 + G108-G112 consistent observations).

### Problem

When sibling theorems share elaborated proof structure across
multiple INDEPENDENT measurement layers — AST recursor /
tactic-token sequence / citation graph / Expr-invocation count /
Expr-node count / Expr-string length — abstraction is no longer
"could be cleaner" but **overdetermined**.

### Example: L1 LeibnizAlgLift (6-layer byte-identical)

| Layer | Measure | All 4 siblings |
|-------|---------|----------------|
| AST G90 | recursor-tag profile | identical |
| Syntax G91 | tactic-token count | 48 each |
| Citation G92 | cite multiset | 43 each |
| Expr G102 | const-invocations | 206,914 each |
| Expr G103 | total Expr-node count | 628,271 each |
| Expr G106 | normalised string length | 3,309,145 chars each |

Six independent measurements agree byte-identical across 4
siblings.  The only difference is the α/β factor knob (0.1 % at
position 30 of 48 tactic-tokens).

### Solution

Use n-layer agreement as **abstraction-priority ordering**.  Pairs
agreeing at one layer (G92 cite identity) are candidates; pairs
agreeing at 3+ layers are high-confidence; pairs agreeing at 6
layers are **overdetermined**.

### Concrete metric

```
abstraction_confidence = #layers_agreeing × per_layer_strictness
```

L1's 6-layer match at 50 % mass cut = **single largest
abstraction target in the corpus**.

### Where applied

  · G106 §3 sketches L1's parametric form.
  · G114 §4 — CayleyDickson `*.ext` / `conj_ne_id` byte-
    identical pairs (smaller scale).
  · G110 §5 — FluxMVT forward/backward byte-identical pairs.
  · G111 §4 — Cohomology Universal Prop52/53 + Hodge Prop 5_k
    quartet.

### Generalisation

When designing abstraction priorities, prefer overdetermined
candidates (5+ layer byte-identical) over single-layer cluster
candidates.  The mass × overdetermination product is the right
ranking metric.

---


## Pattern #15 — Three-level "Derived from Raw" distinction (G104)

**Reference**: full spec in `seed/THEOREM_METHODOLOGY_SUITE.md` §TH-2.

**Summary**: The phrase "X derives from Raw" has three distinct
technical meanings:

  · **(α) Logical derivability** — `#print axioms` empty (TRUE for DRLT).
  · **(β) Structural-content derivability** — math content derives
    from Raw via atomic_iff_five → alive_iff_clause4_alive →
    six_theorem chain (TRUE for DRLT).
  · **(γ) Operational/definitional reduction** — every Expr
    reduces to Raw atoms (FALSE BY DESIGN — encapsulation efficiency).

(α) + (β) hold; (γ) is FALSE BY DESIGN.  Don't conflate the levels.

Full text + worked examples (Real213, FluxMVT, Cohomology):
`seed/THEOREM_METHODOLOGY_SUITE.md` §TH-2.


## Pattern #16 — Decide-finitism quantitative profile (G100)

**Reference**: full spec in `seed/THEOREM_METHODOLOGY_SUITE.md` §TH-3.

**Summary**: Pattern #2 (decide-finitism) has measurable footprint:

  · **36 % of theorems** are pure `[decide]` proofs (G91).
  · **8 % of theorems** are decide-verified negative claims
    (135 falsifiers from G100).
  · Combined **~44 % decide-routed** at one polarity or the other.
  · `Bool.casesOn` is the corpus's largest recursor (1,681 invocations
    / 634 callers; G105).

Distinguishability (`≠`) dominates negation (78 % of falsifiers) —
consistent with Raw's distinguishability primitive in operational form.

Full quantitative profile + falsifier catalog references:
`seed/THEOREM_METHODOLOGY_SUITE.md` §TH-3 and
`catalogs/falsifier-roster.md`.


## Pattern #17 — Framework-internal subsumption (Bishop / classical)

**Discovered**: 2026-05-21 meta-analysis (G108).

### Problem

Constructing ℝ classically requires ε-N moduli (Bishop's
constructive ℝ) or Cauchy quotients (Cauchy's ℝ).  Both involve
non-trivial machinery.

### DRLT reframe (`AsLensOutput.lean`, user 2026-04-26 insight)

> "Aren't there infinitely many different ways to extract natural
> numbers from 213? Of course reals exist then. Computation? You
> can always pick any way to operate on those infinitely many
> natural numbers."

> "The Bishop program itself is redundant within 213 — the Lens
> space of 213 already contains the reals."

The Lens output function space `Raw → Bool` (i.e., `Nat → Nat →
Bool` cut functions) already contains the reals.  Specific
operations like `cutSum`, `cutMul` are CHOICES of combine
function in this space.  No external construction needed.

### Concrete idiom

```lean
abbrev RealAsLensOutput := Nat → Nat → Bool

def cutSum : RealAsLensOutput → RealAsLensOutput → RealAsLensOutput
def cutMul : RealAsLensOutput → RealAsLensOutput → RealAsLensOutput
-- Both are "valid choices" within the framework
```

### Where applied

  · G108 §2 — articulates the subsumption.
  · G108 §3 layer hierarchy — shows the layered architecture
    that operationalises the doctrine.
  · G110 §"213-native vs classical" — analytic analogue:
    derivative = localDivergence, FTC = dyadic Stokes, MVT =
    cohomological balance.  Subsumes classical limit-based
    analysis.

### Generalisation

When a classical concept (real number, derivative, integral,
cup product, etc.) requires a non-trivial construction
externally, look for whether the **Lens-output space already
contains it** as a choice of operation.  Real213 (G108) and
FluxMVT (G110) demonstrate the pattern.

---


## Pattern #18 — Byte-identical Expr cross-domain bridges

**Discovered**: 2026-05-22 meta-analysis (G109).

### Problem

Math and physics theorems may share more than analogical
structure — at the elaborated `Expr` level, they may produce
literally identical terms post-normalisation.

### Discovery method

Group all decls by 14-dimensional `Expr`-shape vector
(`tools/_ast_shape_rows.tsv` from G103).  Filter to vectors
shared by ≥ 2 decls across distinct top-level namespaces.

### Quantification

  · 109 cross-namespace byte-identical groups in DRLT.
  · 25 of these span Math ↔ Physics (substantive bridges).
  · 5-way structural identities: K_5 / K_25 first Betti ≡
    inverse-α₃ ≡ SU(NS) adjoint, etc. (G109 ★ Bridges 20-25).

### Where applied

  · G109 — full scan and characterisation.
  · `catalogs/cross-domain-identifications.md` — 10 named CDIs.
  · G111 §5 / G112 §6 / others — Cohomology +
    HodgeConjecture's role as math-side anchor for the bridges.

### Generalisation

Use shape-vector grouping as a routine analysis: after any
substantial new theorem addition, re-run the scan to catch
new cross-domain identifications.  These are LOAD-BEARING
math-physics connections, not analogies.

---


## Pattern #19 — Forward/backward (α/β) factor-knob byte-identical pair

**Discovered**: 2026-05-21 meta-analysis (G106 L1, G110 FluxMVT,
G114 CayleyDickson).

### Problem

Many DRLT proofs come in forward/backward, α/β, real/imaginary,
positive/negative orientation pairs.  Each pair often produces
byte-identical Expr post-normalisation modulo the orientation
choice.

### Examples discovered

| Pair | Layer | Size |
|------|-------|------|
| L1 LeibnizAlgLift α/β factor (4 siblings) | 6-layer agreement | 6.6 M chars |
| FluxMVT forward/backward (5 pairs) | Expr nodes | 30K nodes |
| Bilinear cupAW_add_left/right | Expr nodes | 113K each |
| CayleyDickson sub_im / sub_re pair | Expr nodes | 1K |
| ZI / ZSqrt2 / ZOmega conjugation pairs | Expr nodes | various |

### Reading

The pair is parameterised by an orientation knob.  The two
instantiations are **literal same proof** with the knob value
swapped.

### Concrete form

```lean
theorem foo_α (x y : T) : property α x y :=
  -- forward version
theorem foo_β (x y : T) : property β x y :=
  -- backward version (byte-identical to α post-normalisation)
```

### Solution

Lift to one parametric:

```lean
theorem foo_factor (factor : α ∨ β) (x y : T) :
    property factor x y := ...
```

OR keep both names as `@[reducible]` aliases of one general
form.

### Where applied

  · G106 §3 — L1 LeibnizAlgLift refined signature.
  · G110 §5 — FluxMVT forward/backward pairs.
  · G111 + G114 — Cohomology + CayleyDickson byte-identical
    pair groups.

### Generalisation

The factor-knob pair pattern generalises to **oriented
structures**: oriented manifolds, oriented homology, signed
measures, chirality.  Any signed/oriented framework will
likely produce byte-identical pairs at the Expr level.

---


## Pattern #20 — Multiple Lens choices for the same categorical concept

**Discovered**: 2026-05-22 meta-analysis (G108 + G110 + G111
G85 disclosure).

### Problem

A categorical concept (cup product, derivative, integral, cut
function) may admit multiple framework-internal realisations.
Picking one as "canonical" loses generality; defining all as
distinct Lens choices preserves freedom.

### Examples discovered

**Cup product** (G85, G111 §6): two distinct cups coexist in
Cohomology:
  · `cupAW` — Alexander-Whitney standard form
  · `cup` (lex-projection) — boundary-endpoint correction form

Both ∀(n, k, l) proven PURE.  Both serve distinct roles.

**Derivative** (G110 §2): three forms:
  · classical limit (not used in DRLT)
  · `localDivergence` (213-native: flux × 2^expE)
  · `IsDifferentiable` (`Differentiation/`, explicit derivative
    data)

DRLT formalises ALL three as framework-internal choices.

**Cut function** (G108 §1): three carriers for real numbers:
  · `Real213` struct (Raw sequence + modulus)
  · `RealAsLensOutput := Nat → Nat → Bool` (Lens output abbrev)
  · `DyadicBracket` (Analysis-time finite data structure)

All three coexist; bridges connect them.

### Reading

DRLT systematically refuses to pick "the canonical" form when
multiple framework-internal realisations exist.  This is
consistent with the Lens-output doctrine — each choice is a
Lens output of the underlying Raw structure.

### Where applied

  · G108 §2 (AsLensOutput doctrine).
  · G110 §2 + §6 (three derivative forms).
  · G111 §6 (cup vs cupAW, G85 self-correction).

### Generalisation

When introducing a new categorical concept, formalise multiple
Lens-output realisations rather than picking one.  This
generalises Pattern #14 (framework-internal subsumption) to
**multiplicity within the framework** rather than just
subsuming external constructions.

---

