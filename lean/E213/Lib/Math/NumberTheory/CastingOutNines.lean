import E213.Meta.Nat.PolyNatMTactic
import E213.Meta.Tactic.NatHelper
import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum

/-!
# CastingOutNines — the divisibility-rule core `bᵏ ≡ 1 (mod b−1)`

The arithmetic behind casting-out-nines / divisibility rules: every power of `b` is `≡ 1`
modulo `b − 1` (writing `b = m + 1`, every power of `m+1` is `≡ 1 (mod m)`), because
`b ≡ 1 (mod b−1)`.  Hence `b−1 ∣ bᵏ − 1`, and a base-`b` numeral is congruent to its digit
sum mod `b−1` (the `b=10` case is casting-out-nines).

All zero-axiom (pure `Nat`, no subtraction in the core identity).
-/

namespace E213.Lib.Math.NumberTheory.CastingOutNines

open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum (sumTo)

/-- ★★ **`(m+1)ᵏ ≡ 1 (mod m)`**: every power of `m+1` is `m·c + 1` for some `c` — the
    `bᵏ ≡ 1 (mod b−1)` rule (with `b = m+1`), subtraction-free. -/
theorem pow_succ_base_mod (m : Nat) : ∀ k, ∃ c, (m + 1) ^ k = m * c + 1
  | 0     => ⟨0, by rw [Nat.pow_zero, Nat.mul_zero, Nat.zero_add]⟩
  | k + 1 => by
      obtain ⟨c, hc⟩ := pow_succ_base_mod m k
      refine ⟨c * (m + 1) + 1, ?_⟩
      rw [Nat.pow_succ, hc]; ring_nat

/-- ★ **`(b−1) ∣ bᵏ − 1`** (`b = m+1`): the divisibility consequence — `m ∣ (m+1)ᵏ − 1`. -/
theorem base_pred_dvd_pow_pred (m k : Nat) : m ∣ ((m + 1) ^ k - 1) := by
  obtain ⟨c, hc⟩ := pow_succ_base_mod m k
  refine ⟨c, ?_⟩
  rw [hc, E213.Tactic.NatHelper.add_sub_cancel_right]


/-- ★★★ **Geometric series sum** (the exact quotient behind casting-out-nines):
    `(b−1)·Σ_{j<k} bʲ + 1 = bᵏ` (with `b = m+1`): `m·Σ_{j<k} (m+1)ʲ + 1 = (m+1)ᵏ`.  So
    `Σ_{j<k} bʲ` is exactly the cofactor `c` of `pow_succ_base_mod`, and `bᵏ − 1 = (b−1)·Σ bʲ`. -/
theorem geom_sum (m : Nat) : ∀ k,
    m * sumTo k (fun j => (m + 1) ^ j) + 1 = (m + 1) ^ k
  | 0     => by rw [show sumTo 0 (fun j => (m + 1) ^ j) = 0 from rfl,
                    Nat.mul_zero, Nat.zero_add, Nat.pow_zero]
  | k + 1 => by
      have ih := geom_sum m k
      show m * (sumTo k (fun j => (m + 1) ^ j) + (m + 1) ^ k) + 1 = (m + 1) ^ (k + 1)
      rw [Nat.mul_add, Nat.pow_succ,
          Nat.add_right_comm (m * sumTo k (fun j => (m + 1) ^ j)) (m * (m + 1) ^ k) 1, ih]
      ring_nat

end E213.Lib.Math.NumberTheory.CastingOutNines
