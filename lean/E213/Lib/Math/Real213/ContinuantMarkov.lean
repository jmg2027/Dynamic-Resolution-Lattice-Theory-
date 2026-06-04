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
open E213.Lib.Math.Real213.SternBrocotMarkov (genL genR)
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

end E213.Lib.Math.Real213.ContinuantMarkov
