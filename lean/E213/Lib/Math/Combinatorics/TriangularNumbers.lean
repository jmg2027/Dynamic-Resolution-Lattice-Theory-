import E213.Lib.Math.Combinatorics.PowerSums

/-!
# Triangular-number identities (∅-axiom)

`tri n = 0 + 1 + … + n` (`sumTo (n+1) id`), reusing `PowerSums.gauss_sum`
(`2·tri n = n(n+1)`) as the engine.  The classical square-relations, genuinely
absent (the corpus `tri` maps use division or are order-only):

  * `tri_succ` : `tri (n+1) = tri n + (n+1)` (the recurrence).
  * `tri_add_succ` : `tri n + tri (n+1) = (n+1)²` — consecutive triangulars sum to a
    perfect square.
  * ★ `eight_tri_add_one` : `8·tri n + 1 = (2n+1)²` — the triangular ↔ odd-square
    bijection.

All in subtraction-free (cross-multiplied) form, closed by `ring_nat`.  ∅-axiom.
-/

namespace E213.Lib.Math.Combinatorics.TriangularNumbers

open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum (sumTo sumTo_succ)
open E213.Lib.Math.Combinatorics.PowerSums (gauss_sum)

/-- The n-th triangular number `0 + 1 + … + n`. -/
def tri (n : Nat) : Nat := sumTo (n + 1) (fun i => i)

/-- **Bridge** (re-export of `gauss_sum`): `2·tri n = n(n+1)`. -/
theorem two_tri (n : Nat) : 2 * tri n = n * (n + 1) := gauss_sum n

/-- **Recurrence** (shift form): `tri (n+1) = tri n + (n+1)`. -/
theorem tri_succ (n : Nat) : tri (n + 1) = tri n + (n + 1) := by
  show sumTo (n + 1 + 1) (fun i => i) = sumTo (n + 1) (fun i => i) + (n + 1)
  rw [sumTo_succ]

/-- **Consecutive triangulars sum to a square** (cross form): `2·(tri n + tri (n+1)) = 2(n+1)²`. -/
theorem two_tri_add_succ (n : Nat) :
    2 * (tri n + tri (n + 1)) = 2 * ((n + 1) * (n + 1)) := by
  have h1 := two_tri n
  have h2 := two_tri (n + 1)
  have hsplit : 2 * (tri n + tri (n + 1)) = 2 * tri n + 2 * tri (n + 1) := by ring_nat
  rw [hsplit, h1, h2]
  ring_nat

/-- ★ **Consecutive triangulars sum to a square**: `tri n + tri (n+1) = (n+1)²`. -/
theorem tri_add_succ (n : Nat) : tri n + tri (n + 1) = (n + 1) * (n + 1) :=
  Nat.eq_of_mul_eq_mul_left (by decide) (two_tri_add_succ n)

/-- ★ **The 8T+1 identity** (triangular ↔ odd square): `8·tri n + 1 = (2n+1)²`. -/
theorem eight_tri_add_one (n : Nat) :
    8 * tri n + 1 = (2 * n + 1) * (2 * n + 1) := by
  have h := two_tri n
  have hsplit : 8 * tri n = 4 * (2 * tri n) := by ring_nat
  rw [hsplit, h]
  ring_nat

/-- Concrete smoke: `tri 3 = 6`, and `8·6 + 1 = 49 = 7²`. -/
theorem tri_smoke : tri 3 = 6 ∧ 8 * tri 3 + 1 = 7 * 7 := by
  refine ⟨by decide, by decide⟩

end E213.Lib.Math.Combinatorics.TriangularNumbers
