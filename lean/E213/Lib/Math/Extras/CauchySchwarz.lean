import E213.Term.Tactic.Nat213

/-!
# Cauchy-Schwarz / AM-GM (atomic, Nat-side, ∅-axiom)

Closes the deferral noted in `Measure/INDEX.md` and `Functional/INDEX.md`:
the elementary inequality `2 · a · b ≤ a² + b²` for `a, b : Nat`.

213-native proof: case-split on `a ≤ b ∨ b ≤ a`, write the larger
as `smaller + d`, expand `(a + d)² = a² + 2 · a · d + d²`, observe
`a² + (a+d)² = 2 · a · (a+d) + d²`.  All term-mode, no propext leak.

Used by `Measure/Lp.lean` (Hölder atom) and `Functional/InnerProduct.lean`
(Cauchy-Schwarz on the diagonal).
-/

namespace E213.Lib.Math.Extras.CauchySchwarz

open E213.Tactic.Nat213 (mul_assoc add_mul)

/-- Term-mode `(a + d)² = a² + 2·a·d + d²`. -/
theorem sq_add (a d : Nat) :
    (a + d) * (a + d) = a * a + 2 * (a * d) + d * d := by
  show (a + d) * (a + d) = a * a + 2 * (a * d) + d * d
  rw [Nat.mul_add (a + d) a d]
  rw [add_mul a d a, add_mul a d d]
  rw [Nat.mul_comm d a]
  show a * a + a * d + (a * d + d * d) = a * a + 2 * (a * d) + d * d
  rw [← Nat.add_assoc (a * a + a * d) (a * d) (d * d)]
  rw [Nat.add_assoc (a * a) (a * d) (a * d)]
  show a * a + (a * d + a * d) + d * d = a * a + 2 * (a * d) + d * d
  show a * a + (a * d + a * d) + d * d = a * a + 2 * (a * d) + d * d
  have h : a * d + a * d = 2 * (a * d) := by
    show a * d + a * d = (1 + 1) * (a * d)
    rw [add_mul 1 1 (a * d), Nat.one_mul]
  rw [h]

/-- Term-mode helper: `a + a = 2 · a`. -/
theorem add_self_eq_two_mul (a : Nat) : a + a = 2 * a := by
  show a + a = (1 + 1) * a
  rw [add_mul 1 1 a, Nat.one_mul]

/-- Algebraic identity in `(a, d)` form:
    `a² + (a+d)² = 2·a·(a+d) + d²`. -/
theorem cs_expand (a d : Nat) :
    a * a + (a + d) * (a + d) = 2 * (a * (a + d)) + d * d := by
  rw [sq_add a d]
  show a * a + (a * a + 2 * (a * d) + d * d)
        = 2 * (a * (a + d)) + d * d
  rw [Nat.mul_add a a d, Nat.mul_add 2 (a * a) (a * d)]
  rw [Nat.add_assoc (a * a) (a * a + 2 * (a * d)) (d * d)
        |>.symm]
  show (a * a + (a * a + 2 * (a * d))) + d * d
        = 2 * (a * a) + 2 * (a * d) + d * d
  rw [Nat.add_assoc (a * a) (a * a) (2 * (a * d)) |>.symm]
  show (a * a + a * a + 2 * (a * d)) + d * d
        = 2 * (a * a) + 2 * (a * d) + d * d
  rw [add_self_eq_two_mul (a * a)]

/-- ★ AM-GM-style cross term: `2·a·b ≤ a² + b²` (Cauchy-Schwarz
    on a 1-bracket cover, Nat side; ∅-axiom). -/
theorem two_mul_le_sq_add_sq (a b : Nat) :
    2 * (a * b) ≤ a * a + b * b := by
  rcases Nat.le_total a b with hab | hba
  · -- case a ≤ b: write b as a + (b - a) = a + d
    have hb : a + (b - a) = b := E213.Tactic.Nat213.add_sub_of_le hab
    have hgoal : 2 * (a * (a + (b - a))) ≤
                 a * a + (a + (b - a)) * (a + (b - a)) := by
      rw [cs_expand a (b - a)]
      exact Nat.le_add_right _ _
    rw [hb] at hgoal
    exact hgoal
  · -- case b ≤ a: symmetric.  Swap and reduce.
    have ha : b + (a - b) = a := E213.Tactic.Nat213.add_sub_of_le hba
    have hgoal : 2 * (b * (b + (a - b))) ≤
                 b * b + (b + (a - b)) * (b + (a - b)) := by
      rw [cs_expand b (a - b)]
      exact Nat.le_add_right _ _
    rw [ha] at hgoal
    -- hgoal : 2 * (b * a) ≤ b * b + a * a
    rw [Nat.mul_comm a b, Nat.add_comm (a * a) (b * b)]
    exact hgoal

end E213.Lib.Math.Extras.CauchySchwarz
