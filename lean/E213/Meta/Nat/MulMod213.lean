import E213.Meta.Nat.AddMod213
import E213.Meta.Tactic.NatHelper
/-!
# 213-native `Nat.mul_mod` (∅-axiom, Math layer)
-/

namespace E213.Meta.Nat.MulMod213

open E213.Meta.Nat.AddMod213 (div_add_mod add_mod_gen)
open E213.Tactic.NatHelper (add_mul_mod_self_pure add_mul mul_assoc)

/-- `(a * b) % n = ((a % n) * b) % n`.  PURE. -/
theorem mul_mod_left_pure (a b n : Nat) :
    (a * b) % n = ((a % n) * b) % n := by
  have hdiv : n * (a / n) + a % n = a := div_add_mod a n
  -- Rewrite a * b using hdiv (only once via `have`).
  have h_lhs : a * b = (n * (a / n) + a % n) * b := by rw [hdiv]
  rw [h_lhs]
  rw [add_mul]
  rw [Nat.add_comm]
  have h_rearrange : n * (a / n) * b = a / n * b * n := by
    rw [Nat.mul_comm n (a / n)]
    rw [mul_assoc]
    rw [Nat.mul_comm n b]
    rw [← mul_assoc]
  rw [h_rearrange]
  exact add_mul_mod_self_pure ((a % n) * b) n ((a / n) * b)

/-- `(a * b) % n = (a * (b % n)) % n`.  PURE. -/
theorem mul_mod_right_pure (a b n : Nat) :
    (a * b) % n = (a * (b % n)) % n := by
  rw [Nat.mul_comm a b, Nat.mul_comm a (b % n)]
  exact mul_mod_left_pure b a n

/-- `(a * b) % n = ((a % n) * (b % n)) % n`.  PURE. -/
theorem mul_mod_pure (a b n : Nat) :
    (a * b) % n = ((a % n) * (b % n)) % n := by
  rw [mul_mod_left_pure a b n]
  rw [mul_mod_right_pure (a % n) b n]

end E213.Meta.Nat.MulMod213
