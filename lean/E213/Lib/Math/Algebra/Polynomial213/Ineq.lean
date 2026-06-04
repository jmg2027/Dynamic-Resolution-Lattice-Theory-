import E213.Lib.Math.Algebra.Polynomial213.Sound

/-!
# Polynomial213.Ineq — inequality witness pattern (∅-axiom)

Polynomial inequality `eval p x ≤ eval q x` is reduced to providing
a witness `r : Poly` such that `add p r = q` (by `rfl`).  Then
`eval_le_of_add` gives the inequality automatically.

Example:
  `(2k+1)(2k+3) ≤ 4(k+1)²` ↔ `[3,8,4] + [1,0,0] = [4,8,4]` (rfl)
-/

namespace E213.Polynomial213

/-- If `add p r = q`, then `eval p x ≤ eval q x`.  Witness pattern:
    `r` is the (positive) polynomial difference `q - p`. -/
theorem eval_le_of_add (p q r : Poly) (x : Nat)
    (h : add p r = q) : eval p x ≤ eval q x := by
  have h1 : eval p x + eval r x = eval q x := by
    rw [← eval_add p r x, h]
  exact h1 ▸ Nat.le_add_right (eval p x) (eval r x)

/-- Strict version: if `add p (r1 + 1) = q`, then `eval p x < eval q x`. -/
theorem eval_lt_of_add_succ (p q r : Poly) (x : Nat)
    (h : add p (add r (C 1)) = q) : eval p x < eval q x := by
  have hrc : eval (add r (C 1)) x = eval r x + 1 := by
    rw [eval_add, eval_C]
  have h1 : eval p x + (eval r x + 1) = eval q x := by
    rw [← hrc, ← eval_add p _ x, h]
  exact h1 ▸ Nat.lt_add_of_pos_right (Nat.zero_lt_succ (eval r x))

end E213.Polynomial213
