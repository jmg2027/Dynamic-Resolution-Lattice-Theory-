import E213.Lib.Math.NumberTheory.ModArith.MulOrder

/-!
# Fermat fixed-point form — the Frobenius fixed point `aᵖ ≡ a (mod p)`

The unit form `a^(p−1) % p = 1` (`MulOrder.fermat`) holds only for a unit `1 ≤ a < p`.
Its companion — the **Frobenius fixed-point** statement `aᵖ ≡ a (mod p)` (the `x ↦ xᵖ`
map fixing every residue) — holds for *all* `a`, including `a ≡ 0`, where the unit form
is silent.

  * `fermat_fixed_unit` — `0 < a < p ⟹ aᵖ % p = a` (the clean unit case).
  * ★ `fermat_fixed_point` — `∀ a, aᵖ % p = a % p` (Frobenius fixes every residue).

Both ∅-axiom.
-/

namespace E213.Lib.Math.NumberTheory.ModArith.FermatFixedPoint

open E213.Lib.Math.NumberTheory.ModArith.MulOrder (fermat)
open E213.Lib.Math.NumberTheory.ModArith.CubeFromFLT (pow_add_pure)
open E213.Meta.Nat.MulMod213 (mul_mod_pure)
open E213.Meta.Nat.AddMod213 (mod_mod zero_mod)
open E213.Meta.Nat.ModPow213 (pow_mod_base)

/-- **Fermat fixed point, unit case**: for a prime `p` and `0 < a < p`, `aᵖ % p = a`.
    From `aᵖ = a^(p−1) · a` and `a^(p−1) % p = 1`. -/
theorem fermat_fixed_unit (a p : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p)
    (ha0 : 0 < a) (halt : a < p) : a ^ p % p = a := by
  have hf : a ^ (p - 1) % p = 1 := fermat a p hp hpr ha0 halt
  -- p = (p−1) + 1
  have hsucc : (p - 1) + 1 = p := Nat.succ_pred_eq_of_pos (Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_of_lt hp))
  have hsplit : a ^ p = a ^ (p - 1) * a := by
    have h1 : a ^ (p - 1) * a = a ^ ((p - 1) + 1) := by
      rw [pow_add_pure a (p - 1) 1, Nat.pow_one]
    rw [h1, hsucc]
  calc a ^ p % p
      = (a ^ (p - 1) * a) % p := by rw [hsplit]
    _ = (a ^ (p - 1) % p * (a % p)) % p := mul_mod_pure _ _ p
    _ = (1 * (a % p)) % p := by rw [hf]
    _ = (a % p) % p := by rw [Nat.one_mul]
    _ = a % p := mod_mod a p
    _ = a := Nat.mod_eq_of_lt halt

/-- ★ **Fermat fixed point (Frobenius)**: for a prime `p`, `aᵖ ≡ a (mod p)` for *all* `a`.
    Reduce `a` mod `p`: `aᵖ % p = (a%p)ᵖ % p`; the residue `r = a%p < p` is either `0`
    (`0ᵖ % p = 0`) or a unit (`fermat_fixed_unit`). -/
theorem fermat_fixed_point (a p : Nat) (hp : 1 < p) (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p) :
    a ^ p % p = a % p := by
  -- work with the residue r = a % p
  have hreduce : a ^ p % p = (a % p) ^ p % p := pow_mod_base a p p
  have hrlt : a % p < p := Nat.mod_lt a (Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_of_lt hp))
  rcases Nat.eq_zero_or_pos (a % p) with h0 | hpos
  · -- residue 0:  aᵖ % p = 0ᵖ % p = 0 = a % p
    rw [hreduce, h0]
    have hp0 : 0 < p := Nat.lt_of_lt_of_le Nat.zero_lt_one (Nat.le_of_lt hp)
    rw [Nat.zero_pow hp0, zero_mod]
  · -- residue a unit:  (a%p)ᵖ % p = a % p
    rw [hreduce]
    exact fermat_fixed_unit (a % p) p hp hpr hpos hrlt

end E213.Lib.Math.NumberTheory.ModArith.FermatFixedPoint
