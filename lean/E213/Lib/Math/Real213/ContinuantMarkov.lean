import E213.Lib.Math.Real213.SternBrocotMarkov
import E213.Lib.Math.Real213.Continuant

/-!
# The continuant ↔ Markov-generator bridge (and its obstruction)

`Real213/Continuant` placed the continuant `K[a₁,…,aₙ]` inside the `Mat2` algebra as the `(1,1)`-entry
of `∏ᵢ [[aᵢ,1],[1,0]]` (`contMatProd`).  This file tests the next rung toward `markovNum p = (mNode p).c`:
can the Markov tree's generators `genL`, `genR` be written as continuant-matrix words?

The answer is **asymmetric**, and that asymmetry is the content:

  * **`genL` is continuant-native**: `genL = [[2,1],[1,1]] = [[1,1],[1,0]]² = contMatProd [1,1]` — the
    square of the Fibonacci/`M(1)` matrix.  (So the left spine of the tree is exactly the all-`1`
    continued fraction = the Fibonacci/φ spine, consistent with the golden self-reference fixed point.)

  * **`genR` is NOT a positive continuant word**: a continuant matrix `∏[[aᵢ,1],[1,0]]` with every
    `aᵢ ≥ 1` has `(1,1)`-entry `K[a₁…aₙ] ≥ (1,2)`-entry `K[a₁…aₙ₋₁]` (a longer continuant dominates its
    prefix).  But `genR = [[3,4],[2,3]]` has `(1,1) = 3 < 4 = (1,2)` (`genR_a_lt_b`).  So `genR` cannot be
    a continuant matrix on positive partial quotients.

**Consequence.**  The `markovNum`→continuant bridge does **not** go through a naive basis change
(rewriting `genL`/`genR` words as `[[a,1],[1,0]]` words): one generator is not a continuant matrix at all.
The classical Frobenius continuant formula `m_{p/q} = K(CF-shape)` instead routes through the **Cohn
matrix** `tr/3` (`mNode` has `tr = 3·markovNum`, `mInterval_shape`; `C² ≡ −I (mod c)`, `cohn_sq_neg_one_mod`)
and the **doubled Christoffel word** — a larger development than a single basis-change rung.  This file
records that boundary precisely, with the one clean continuant-native generator (`genL`) and the
machine-checked obstruction (`genR`).
-/

namespace E213.Lib.Math.Real213.ContinuantMarkov

open E213.Lib.Math.Real213.ModularElliptic (Mat2 mul)
open E213.Lib.Math.Real213.SternBrocotMarkov (genL genR markovNum mInterval mInterval_det
  det2 det2_mul mInterval_shape markoff_vieta_trace markoff_vieta_trace_R)
open E213.Lib.Math.Real213.Continuant (contMat contMatProd continuant continuant_eq_contMatProd)

/-- **`genL` is the all-`1` continuant word** `[[1,1],[1,0]]² = contMatProd [1,1]` — the square of the
    Fibonacci matrix.  The left generator of the Markov tree is continuant-native (the Fibonacci/φ spine). -/
theorem genL_eq_contMatProd : contMatProd [1, 1] = genL := rfl

/-- Consistency with the continuant value: the `(1,1)`-entry of `genL` (as the continuant word `[1,1]`)
    is `continuant [1,1] = 2`. -/
theorem genL_a_eq_continuant : genL.a = ((continuant [1, 1] : Nat) : Int) := by
  rw [← genL_eq_contMatProd]; exact continuant_eq_contMatProd [1, 1]

/-- **`genR` is not a positive continuant matrix**: its `(1,1)`-entry is strictly below its `(1,2)`-entry
    (`3 < 4`), impossible for `∏[[aᵢ,1],[1,0]]` with all `aᵢ ≥ 1` (where `(1,1) = K[full] ≥ K[prefix] =
    (1,2)`).  So the `markovNum`→continuant bridge is not a naive `genL`/`genR` basis change. -/
theorem genR_a_lt_b : genR.a < genR.b := by decide

/-! ## The continuant-native Cohn Markov generator, and the bridge subtlety

Over the standard Cohn generators `A = [[2,1],[1,1]] = contMatProd [1,1]` and `B = [[5,2],[2,1]] =
contMatProd [2,2]`, every word produces a Markov number as `tr/3` (Cohn), and by `contMatProd_trace_cons`
that trace is a **continuant** — so this is a continuant-native Markov-number generator.  But its per-word
indexing is *not* the repo tree's path indexing: the genuine correspondence is the run-length /
Christoffel cutting-sequence map, not a naive wrap of the path (ruled out below). -/

/-- The Cohn word of a binary word: `true ↦ A = [1,1]`, `false ↦ B = [2,2]` (block concatenation). -/
def cohnWord : List Bool → List Nat
  | [] => []
  | true :: bs => 1 :: 1 :: cohnWord bs
  | false :: bs => 2 :: 2 :: cohnWord bs

/-- The Cohn trace `tr(∏ A/B blocks)` — three times the Markov number of the word (by `contMatProd_trace_cons`
    this is a continuant expression). -/
def cohnTrace (bs : List Bool) : Int := (contMatProd (cohnWord bs)).a + (contMatProd (cohnWord bs)).d

/-- ★★★★ **The continuant-native Cohn generator produces the Markov numbers** as `tr/3`:
    `A, B, AB, AAB, ABB ↦ 1, 2, 5, 13, 29` (traces `3, 6, 15, 39, 87`). -/
theorem cohnTrace_markov_examples :
    cohnTrace [true] = 3 ∧ cohnTrace [false] = 6 ∧ cohnTrace [true, false] = 15
    ∧ cohnTrace [true, true, false] = 39 ∧ cohnTrace [true, false, false] = 87 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- **The naive path→word bridge fails on mixed paths.**  The formula `3·markovNum p = cohnTrace
    (true :: p ++ [false])` holds for single-run paths (`[]`, `[true]`, `[false]`, `[true,true]`, …) but
    **fails** at the alternating path `[true, false]` (`markovNum = 433`): so the repo path → Cohn word
    correspondence is the genuine *run-length / Christoffel cutting-sequence* map, not a naive wrap.  This
    machine-checked counterexample pins the remaining bridge as the nontrivial one. -/
theorem naive_bridge_fails :
    decide (3 * markovNum [true, false] = cohnTrace [true, true, false, false]) = false := by decide

/-! ## The bridge, proved: `markovNum p = tr(Cohn tree node)/3` (continuant-trace)

The genuine path → Christoffel-word correspondence.  The **Cohn matrix tree** is `mInterval` with the
true Cohn right-seed `B = [[5,2],[2,1]] = contMatProd [2,2]` in place of the repo's conjugate `genR`
(the left seed `cohnA = contMatProd [1,1] = genL` already coincides).  Although the matrices differ
(`genR ≠ B`), the **trace-triple `(tr L, tr R, tr (L·R))` follows a recursion in traces alone** — by the
SL₂ identities `tr(L²R) = tr L·tr(LR) − tr R` (`markoff_vieta_trace`) and its `R`-form — and both trees
share the base `(3, 6, 15)`.  Hence the traces coincide at every node, so `tr(cohn node) = tr(mNode) =
3·markovNum` (`mInterval_shape`).  This is the cutting-sequence bijection at the trace level. -/

/-- Cohn left/right seeds: `cohnA = [[2,1],[1,1]] = genL`, `cohnB = [[5,2],[2,1]]` (standard Cohn `B`). -/
def cohnA : Mat2 := contMatProd [1, 1]
def cohnB : Mat2 := contMatProd [2, 2]

/-- The Cohn matrix tree (`mInterval` recursion with the genuine Cohn seeds). -/
def cInterval : List Bool → Mat2 × Mat2
  | [] => (cohnA, cohnB)
  | true :: t => ((cInterval t).1, mul (cInterval t).1 (cInterval t).2)
  | false :: t => (mul (cInterval t).1 (cInterval t).2, (cInterval t).2)

/-- The Cohn tree node. -/
def cNode (p : List Bool) : Mat2 := mul (cInterval p).1 (cInterval p).2

/-- Both Cohn interval bounds are `SL₂(ℤ)` (det 1). -/
theorem cInterval_det : ∀ path, det2 (cInterval path).1 = 1 ∧ det2 (cInterval path).2 = 1
  | [] => by decide
  | true :: t => by
      obtain ⟨h1, h2⟩ := cInterval_det t
      refine ⟨h1, ?_⟩
      show det2 (mul (cInterval t).1 (cInterval t).2) = 1
      rw [det2_mul, h1, h2]; decide
  | false :: t => by
      obtain ⟨h1, h2⟩ := cInterval_det t
      refine ⟨?_, h2⟩
      show det2 (mul (cInterval t).1 (cInterval t).2) = 1
      rw [det2_mul, h1, h2]; decide

/-- ★★★★★ **The trace-triple of the Cohn tree equals that of the repo tree, at every node.**  Proved by
    the traces-only Vieta recursion (`markoff_vieta_trace(_R)`) from the shared base `(3,6,15)`. -/
theorem cohn_trace_eq : ∀ path,
    ((cInterval path).1.a + (cInterval path).1.d = (mInterval path).1.a + (mInterval path).1.d)
    ∧ ((cInterval path).2.a + (cInterval path).2.d = (mInterval path).2.a + (mInterval path).2.d)
    ∧ ((mul (cInterval path).1 (cInterval path).2).a + (mul (cInterval path).1 (cInterval path).2).d
        = (mul (mInterval path).1 (mInterval path).2).a + (mul (mInterval path).1 (mInterval path).2).d)
  | [] => by refine ⟨?_, ?_, ?_⟩ <;> decide
  | true :: t => by
      obtain ⟨i1, i2, i3⟩ := cohn_trace_eq t
      obtain ⟨d1c, _⟩ := cInterval_det t
      obtain ⟨d1m, _⟩ := mInterval_det t
      refine ⟨i1, i3, ?_⟩
      show (mul (cInterval t).1 (mul (cInterval t).1 (cInterval t).2)).a
           + (mul (cInterval t).1 (mul (cInterval t).1 (cInterval t).2)).d
         = (mul (mInterval t).1 (mul (mInterval t).1 (mInterval t).2)).a
           + (mul (mInterval t).1 (mul (mInterval t).1 (mInterval t).2)).d
      rw [markoff_vieta_trace (cInterval t).1 (cInterval t).2 d1c,
          markoff_vieta_trace (mInterval t).1 (mInterval t).2 d1m, i1, i3, i2]
  | false :: t => by
      obtain ⟨i1, i2, i3⟩ := cohn_trace_eq t
      obtain ⟨_, d2c⟩ := cInterval_det t
      obtain ⟨_, d2m⟩ := mInterval_det t
      refine ⟨i3, i2, ?_⟩
      show (mul (mul (cInterval t).1 (cInterval t).2) (cInterval t).2).a
           + (mul (mul (cInterval t).1 (cInterval t).2) (cInterval t).2).d
         = (mul (mul (mInterval t).1 (mInterval t).2) (mInterval t).2).a
           + (mul (mul (mInterval t).1 (mInterval t).2) (mInterval t).2).d
      rw [markoff_vieta_trace_R (cInterval t).1 (cInterval t).2 d2c,
          markoff_vieta_trace_R (mInterval t).1 (mInterval t).2 d2m, i1, i2, i3]

/-- ★★★★★ **The Frobenius bridge, proved**: `3·markovNum p = tr(Cohn node p)` — the Markov number is the
    trace (over 3) of the Christoffel/Cohn matrix word at path `p`.  Via `cohn_trace_eq` (Cohn trace =
    repo trace) and `mInterval_shape` (repo trace = `3·markovNum`).  Composed with the continuant trace
    identity (`Continuant.contMatProd_trace_cons`), this expresses every Markov number as a continuant —
    the Frobenius (1913) continuant formula, ∅-axiom. -/
theorem markovNum_eq_cohn_trace (path : List Bool) :
    3 * markovNum path
      = (mul (cInterval path).1 (cInterval path).2).a + (mul (cInterval path).1 (cInterval path).2).d := by
  show 3 * (mul (mInterval path).1 (mInterval path).2).c
       = (mul (cInterval path).1 (cInterval path).2).a + (mul (cInterval path).1 (cInterval path).2).d
  rw [(cohn_trace_eq path).2.2, (mInterval_shape path).2.2]

end E213.Lib.Math.Real213.ContinuantMarkov
