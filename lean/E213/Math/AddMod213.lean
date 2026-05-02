import E213.Math.NatDiv213
import E213.Kernel.Tactic.Nat213

/-!
# 213-native `Nat.add_mod` (∅-axiom, Math layer)

Lean-core `Nat.add_mod` brings `propext`.  This ∅-axiom replacement
unblocks `sub_is_multiple_of_p` and the
`signature_eventually_periodic_of_periodic_bits` chain.
-/

namespace E213.Math.AddMod213

open E213.Tactic.Nat213 (sub_add_cancel)
open E213.Math.NatDiv213 (add_mod_right_pos)

/-- `(a + b) % n = (a % n + b) % n` when `0 < n`.  ∅-axiom via
    strong recursion on `a`. -/
theorem add_mod_left {n : Nat} (hn : 0 < n) :
    ∀ (a b : Nat), (a + b) % n = (a % n + b) % n := fun a b =>
  Nat.strongRecOn a (motive := fun a => (a + b) % n = (a % n + b) % n)
    fun a ih => by
      show (a + b) % n = (a % n + b) % n
      by_cases ha : a < n
      · rw [Nat.mod_eq_of_lt ha]
      · have hge : n ≤ a := Nat.le_of_not_lt ha
        have hsub_lt : a - n < a :=
          Nat.sub_lt (Nat.lt_of_lt_of_le hn hge) hn
        have ih' := ih (a - n) hsub_lt
        have hmod_a : a % n = (a - n) % n := Nat.mod_eq_sub_mod hge
        have hadd_eq : a + b = (a - n) + b + n := by
          rw [show (a - n) + b + n = (a - n) + n + b from by
                rw [Nat.add_assoc, Nat.add_comm b n, ← Nat.add_assoc],
              sub_add_cancel hge]
        rw [hadd_eq, add_mod_right_pos hn, ih', hmod_a]

/-- `a % n % n = a % n`.  ∅-axiom. -/
theorem mod_mod (a n : Nat) : a % n % n = a % n := by
  by_cases h : 0 < n
  · exact Nat.mod_eq_of_lt (Nat.mod_lt _ h)
  · have hn0 : n = 0 := Nat.eq_zero_of_not_pos h
    subst hn0
    rw [Nat.mod_zero, Nat.mod_zero]

/-- `(a + b) % n = (a % n + b % n) % n` when `0 < n`.  ∅-axiom. -/
theorem add_mod {n : Nat} (hn : 0 < n) (a b : Nat) :
    (a + b) % n = (a % n + b % n) % n := by
  rw [add_mod_left hn a b]
  rw [Nat.add_comm (a % n) b, add_mod_left hn b (a % n), Nat.add_comm]

/-- `b * (a / b) + a % b = a` for all `a b`.  ∅-axiom replacement
    for `Nat.div_add_mod` (which leaks propext). -/
theorem div_add_mod : ∀ (a b : Nat), b * (a / b) + a % b = a := fun a b =>
  Nat.strongRecOn a (motive := fun a => b * (a / b) + a % b = a)
    fun a ih => by
      show b * (a / b) + a % b = a
      by_cases hbound : 0 < b ∧ b ≤ a
      · have hsub_lt : a - b < a :=
          Nat.sub_lt (Nat.lt_of_lt_of_le hbound.1 hbound.2) hbound.1
        have ih' := ih (a - b) hsub_lt
        have hd : a / b = (a - b) / b + 1 := by
          rw [Nat.div_eq]; rw [if_pos hbound]
        have hm : a % b = (a - b) % b := by
          rw [Nat.mod_eq]; rw [if_pos hbound]
        rw [hd, hm, Nat.mul_add, Nat.mul_one]
        rw [Nat.add_assoc, Nat.add_comm b _, ← Nat.add_assoc, ih']
        exact sub_add_cancel hbound.2
      · by_cases hb : 0 < b
        · have ha : a < b :=
            Nat.lt_of_not_le (fun h => hbound ⟨hb, h⟩)
          have hd : a / b = 0 := Nat.div_eq_of_lt ha
          have hm : a % b = a := Nat.mod_eq_of_lt ha
          rw [hd, hm, Nat.mul_zero, Nat.zero_add]
        · have hb_eq : b = 0 := Nat.eq_zero_of_not_pos hb
          rw [hb_eq, Nat.zero_mul, Nat.zero_add]
          rw [Nat.mod_eq]
          rw [if_neg (fun h => absurd h.1 (Nat.lt_irrefl _))]

end E213.Math.AddMod213
