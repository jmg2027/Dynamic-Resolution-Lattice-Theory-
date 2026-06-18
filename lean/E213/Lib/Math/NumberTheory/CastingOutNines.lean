import E213.Meta.Nat.PolyNatMTactic
import E213.Meta.Tactic.NatHelper

/-!
# CastingOutNines — the divisibility-rule core `bᵏ ≡ 1 (mod b−1)`

The arithmetic behind casting-out-nines / divisibility rules: every power of `b` is `≡ 1`
modulo `b − 1` (writing `b = m + 1`, every power of `m+1` is `≡ 1 (mod m)`), because
`b ≡ 1 (mod b−1)`.  Hence `b−1 ∣ bᵏ − 1`, and a base-`b` numeral is congruent to its digit
sum mod `b−1` (the `b=10` case is casting-out-nines).

All zero-axiom (pure `Nat`, no subtraction in the core identity).
-/

namespace E213.Lib.Math.NumberTheory.CastingOutNines

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

end E213.Lib.Math.NumberTheory.CastingOutNines
