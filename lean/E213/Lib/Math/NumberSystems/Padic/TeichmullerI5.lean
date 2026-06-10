import E213.Lib.Math.NumberSystems.Padic.TeichmullerUnit
import E213.Meta.Nat.PolyNatMTactic

/-!
# `i₅ = teichmuller(2-lift)` — the 5-adic imaginary unit IS a Teichmüller representative

The 5-adic imaginary unit `i₅ = √(−1) ∈ ℤ_5` (`Hensel.i_5`, digit 0 = `2`) is a primitive 4-th
root of unity (`i_5_pow_four_trunc`: `i₅⁴ ≡ 1`), hence Frobenius-fixed (`i₅⁵ = i₅⁴·i₅ ≡ i₅`).  By
the uniqueness of the Frobenius-fixed lift (`teichmuller_eq_of_fixed`), `i₅` therefore **equals**
the Teichmüller representative of any lift of `2 ∈ 𝔽₅` — it is not an extra structure adjoined to
`ℤ_5` but the canonical `μ₄` representative.

The Frobenius fix `i₅⁵ ≡ i₅` is clean from `Zp.pow_trunc` (`(pow x n).trunc m = (x.trunc m)ⁿ % pᵐ`):
the whole thing lives in `ℤ/5ᵐ`, where `i₅⁴ ≡ 1` gives `i₅⁵ = i₅⁴·i₅ ≡ i₅`.  All ∅-axiom.
-/

namespace E213.Lib.Math.NumberSystems.Padic.TeichmullerI5

open E213.Meta.Nat.MulMod213 (mul_mod_left_pure mul_mod_right_pure)
open E213.Tactic.NatHelper (cases_lt_five)

/-- The canonical lift of `2 ∈ 𝔽₅` to `ℤ_5`: digit 0 is `2`, all higher digits `0`. -/
def lift2 : ZpSeq 5 := ⟨fun k => if k = 0 then ⟨2, by decide⟩ else ⟨0, by decide⟩⟩

/-- `i₅⁴ ≡ 1 (mod 5ⁿ⁺¹)` in **power form** `(i₅.trunc (n+1))⁴ % 5ⁿ⁺¹ = 1`, converted from the
    balanced `i_5_pow_four_trunc` by pulling the inner mods (`mul_mod_left/right_pure`). -/
theorem i5_pow4_mod (n : Nat) : (Zp.i_5.trunc (n + 1)) ^ 4 % 5 ^ (n + 1) = 1 := by
  have h := Zp.i_5_pow_four_trunc n
  rw [Zp.mul_trunc 5 (by decide) (Zp.mul 5 (by decide) Zp.i_5 Zp.i_5)
        (Zp.mul 5 (by decide) Zp.i_5 Zp.i_5) (n + 1),
      Zp.mul_trunc 5 (by decide) Zp.i_5 Zp.i_5 (n + 1),
      ← mul_mod_left_pure (Zp.i_5.trunc (n + 1) * Zp.i_5.trunc (n + 1))
        ((Zp.i_5.trunc (n + 1) * Zp.i_5.trunc (n + 1)) % 5 ^ (n + 1)) (5 ^ (n + 1)),
      ← mul_mod_right_pure (Zp.i_5.trunc (n + 1) * Zp.i_5.trunc (n + 1))
        (Zp.i_5.trunc (n + 1) * Zp.i_5.trunc (n + 1)) (5 ^ (n + 1))] at h
  rw [show (Zp.i_5.trunc (n + 1)) ^ 4
        = Zp.i_5.trunc (n + 1) * Zp.i_5.trunc (n + 1)
          * (Zp.i_5.trunc (n + 1) * Zp.i_5.trunc (n + 1)) from by
        rw [Nat.pow_succ, Nat.pow_succ, Nat.pow_succ, Nat.pow_succ, Nat.pow_zero]; ring_nat]
  exact h

/-- ★ **`i₅` is Frobenius-fixed**: `i₅⁵ ≡ i₅` at every truncation.  `(i₅.trunc m)⁵ = (i₅.trunc m)⁴ ·
    i₅.trunc m ≡ 1 · i₅.trunc m = i₅.trunc m (mod 5ᵐ)` via `i5_pow4_mod`. -/
theorem i5_frob_fixed (m : Nat) :
    (Zp.pow 5 (by decide) Zp.i_5 5).trunc m = Zp.i_5.trunc m := by
  cases m with
  | zero => rfl
  | succ n =>
    rw [Zp.pow_trunc 5 (by decide) Zp.i_5 (n + 1) 5,
        show (Zp.i_5.trunc (n + 1)) ^ 5
            = (Zp.i_5.trunc (n + 1)) ^ 4 * Zp.i_5.trunc (n + 1) from by rw [Nat.pow_succ],
        mul_mod_left_pure ((Zp.i_5.trunc (n + 1)) ^ 4) (Zp.i_5.trunc (n + 1)) (5 ^ (n + 1)),
        i5_pow4_mod n, Nat.one_mul]
    exact Nat.mod_eq_of_lt (ZpSeq.trunc_lt_p_pow (by decide) Zp.i_5 (n + 1))

/-- The half-system `gcd` side-condition for `p = 5` (each `m ∈ {1,2,3,4}` is coprime to `5`). -/
theorem prime_gcd_5 : ∀ m, 0 < m → m < 5 →
    (E213.Lib.Math.NumberTheory.ModArith.ModBezout.modBezout m 5).1 = 1 := by
  intro m h0 h5
  rcases cases_lt_five h5 with h | h | h | h | h
  · exact absurd (h ▸ h0) (by decide)
  · rw [h]; decide
  · rw [h]; decide
  · rw [h]; decide
  · rw [h]; decide

/-- ★★★★ **`i₅ = teichmuller(2-lift)`**: the 5-adic imaginary unit equals the Teichmüller
    representative of the lift of `2 ∈ 𝔽₅`, at every truncation.  The `p = 5` instance made
    fully concrete: `i₅ ∈ μ₄ ⊂ ℤ_5^×` is the canonical Frobenius-fixed lift of its residue. -/
theorem i5_eq_teichmuller (n : Nat) :
    Zp.i_5.trunc (n + 1) = (Zp.teichmuller 5 (by decide) lift2).trunc (n + 1) :=
  Zp.teichmuller_eq_of_fixed 5 (by decide) lift2 Zp.i_5 prime_gcd_5 i5_frob_fixed rfl n

end E213.Lib.Math.NumberSystems.Padic.TeichmullerI5
