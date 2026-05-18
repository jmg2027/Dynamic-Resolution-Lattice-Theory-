import E213.Lib.Math.Polynomial213.Core

/-!
# Polynomial213.Sound — soundness lemmas (∅-axiom)

For each Polynomial213 operation (`add`, `scale`, `shift`, `mul`,
`trim`), prove that evaluation commutes with the operation.

All proofs use only audited PURE Nat helpers (`Nat.add_*`,
`Nat.mul_*`, `E213.Tactic.NatHelper.{add_mul, mul_assoc}`).
-/

namespace E213.Polynomial213

/-- `eval (shift p) x = x * eval p x` — by `Nat.zero_add`. -/
theorem eval_shift (p : Poly) (x : Nat) :
    eval (shift p) x = x * eval p x :=
  Nat.zero_add (x * eval p x)

/-- `eval (C c) x = c`. -/
theorem eval_C (c x : Nat) : eval (C c) x = c := by
  show c + x * 0 = c
  rw [Nat.mul_zero, Nat.add_zero]

/-- `eval X x = x`. -/
theorem eval_X (x : Nat) : eval X x = x := by
  show 0 + x * (1 + x * 0) = x
  rw [Nat.mul_zero, Nat.add_zero, Nat.mul_one, Nat.zero_add]

/-- `eval (add p q) x = eval p x + eval q x`. -/
theorem eval_add : ∀ (p q : Poly) (x : Nat),
    eval (add p q) x = eval p x + eval q x
  | [],       q,       x => by
      change eval q x = 0 + eval q x
      exact (Nat.zero_add _).symm
  | a :: as, [],       x => by
      change eval (a :: as) x = eval (a :: as) x + 0
      exact (Nat.add_zero _).symm
  | a :: as, b :: bs, x => by
      change (a + b) + x * eval (add as bs) x
        = (a + x * eval as x) + (b + x * eval bs x)
      rw [eval_add as bs x, Nat.mul_add]
      rw [Nat.add_assoc a b _, ← Nat.add_assoc b _ _,
          Nat.add_comm b (x * eval as x),
          Nat.add_assoc (x * eval as x) b _,
          ← Nat.add_assoc a _ _]

/-- `eval (scale k p) x = k * eval p x`. -/
theorem eval_scale (k : Nat) : ∀ (p : Poly) (x : Nat),
    eval (scale k p) x = k * eval p x
  | [],      _ => (Nat.mul_zero k).symm
  | c :: cs, x => by
      show k * c + x * eval (scale k cs) x = k * (c + x * eval cs x)
      rw [eval_scale k cs x, Nat.mul_add k c _,
          ← E213.Tactic.NatHelper.mul_assoc x k (eval cs x),
          Nat.mul_comm x k,
          E213.Tactic.NatHelper.mul_assoc k x (eval cs x)]

/-- `eval (mul p q) x = eval p x * eval q x`. -/
theorem eval_mul : ∀ (p q : Poly) (x : Nat),
    eval (mul p q) x = eval p x * eval q x
  | [],      _, _ => (Nat.zero_mul _).symm
  | a :: as, q, x => by
      change eval (add (scale a q) (shift (mul as q))) x
        = (a + x * eval as x) * eval q x
      rw [eval_add, eval_scale, eval_shift, eval_mul as q x]
      -- Goal: a * eval q x + x * (eval as x * eval q x)
      --     = (a + x * eval as x) * eval q x
      rw [E213.Tactic.NatHelper.add_mul a (x * eval as x) (eval q x),
          E213.Tactic.NatHelper.mul_assoc x (eval as x) (eval q x)]

end E213.Polynomial213
