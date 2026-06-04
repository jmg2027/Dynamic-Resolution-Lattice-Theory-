import E213.Lib.Math.NumberSystems.Padic.Teichmuller
import E213.Lib.Math.NumberSystems.Padic.Hensel
/-!
# Real213-p-adic — Teichmüller representatives as roots of unity

The Teichmüller representative `ω(x)` (`Teichmuller.lean`) is the
diagonal limit of the Frobenius iteration `x ↦ x^p`, fixed by
`ω^p ≡ ω`.  For a **unit** `x` (digit-0 coprime to `p`) this fixed
property refines multiplicatively, using the unit-cancellation engine
from `Hensel.lean` (`mul_right_cancel_trunc`, built on `invFull`):

- **`ω(x)^{p−1} ≡ 1`** — `ω(x)` is a `(p−1)`-th root of unity.  `ℤ_p`
  thus contains the full group `μ_{p−1}`, realised explicitly as
  Teichmüller representatives (no projective-limit existence step).

- **Multiplicative decomposition** `x = ω(x) · u` with `u ≡ 1 (mod p)` —
  the canonical split `ℤ_p^× ≃ μ_{p−1} × (1 + p·ℤ_p)`, here as the
  trunc-level factorisation `(ω⁻¹ · x).trunc 1 = 1`.

This is direction **A→B** of
`research-notes/frontiers/G123_padic_next_directions.md`.  Bridge
file: depends on both the Teichmüller construction and the Hensel
inverse, so it lives apart from the dependency-light `Teichmuller.lean`.
-/

namespace E213.Lib.Math.NumberSystems.Padic

/-! ## `ω(x)` is a `(p−1)`-th root of unity

`p = (p−1) + 1`, so `ω^p = ω^(p−1) · ω`.  The Frobenius fix
`ω^p ≡ ω = 1 · ω` then cancels the unit `ω` (its digit-0 equals
`x`'s) on the right, leaving `ω^(p−1) ≡ 1`. -/

/-- **`ω(x)^{p−1} ≡ 1`**: for `p` prime and `x` a unit (digit-0 coprime
    to `p`), the Teichmüller representative is a `(p−1)`-th root of
    unity at every truncation level `n+1`. -/
theorem Zp.teichmuller_pow_pred_trunc (p : Nat) (hp : 1 < p) (x : ZpSeq p)
    (h_gcd : (E213.Lib.Math.NumberTheory.ModArith.ModBezout.modBezout
              (x.digits 0).val p).1 = 1)
    (h_prime_gcd : ∀ m, 0 < m → m < p
                  → (E213.Lib.Math.NumberTheory.ModArith.ModBezout.modBezout m p).1 = 1)
    (n : Nat) :
    (Zp.pow p hp (Zp.teichmuller p hp x) (p - 1)).trunc (n + 1) = 1 := by
  have hp' : 0 < p := Nat.lt_of_succ_lt hp
  have hp_eq : p = (p - 1) + 1 := (Nat.succ_pred_eq_of_pos hp').symm
  -- ω^p = ω^(p−1) · ω  (pow_succ_def at p = (p−1)+1).
  have hpow : Zp.pow p hp (Zp.teichmuller p hp x) p
            = Zp.mul p (Nat.lt_of_succ_lt hp)
                (Zp.pow p hp (Zp.teichmuller p hp x) (p - 1))
                (Zp.teichmuller p hp x) := by
    have h := Zp.pow_succ_def p hp (Zp.teichmuller p hp x) (p - 1)
    rw [← hp_eq] at h
    exact h
  -- (ω^(p−1) · ω).trunc(n+1) = (1 · ω).trunc(n+1)  via the Frobenius fix.
  have key : (Zp.mul p (Nat.lt_of_succ_lt hp)
                (Zp.pow p hp (Zp.teichmuller p hp x) (p - 1))
                (Zp.teichmuller p hp x)).trunc (n + 1)
           = (Zp.mul p (Nat.lt_of_succ_lt hp)
                (ZpSeq.one p hp) (Zp.teichmuller p hp x)).trunc (n + 1) := by
    rw [← hpow, Zp.teichmuller_pow_p_trunc p hp x h_prime_gcd (n + 1),
        Zp.mul_one_left_trunc hp (Zp.teichmuller p hp x) (n + 1)]
  -- Cancel the unit ω on the right: ω^(p−1) ≡ 1.  (ω.digits 0 = x.digits 0.)
  have hcancel := Zp.mul_right_cancel_trunc p hp (Zp.teichmuller p hp x)
    (Zp.pow p hp (Zp.teichmuller p hp x) (p - 1)) (ZpSeq.one p hp) h_gcd n key
  rw [hcancel]
  exact ZpSeq.trunc_one_succ p hp n

/-- Smoke: the 5-adic Teichmüller representative of digit-0 = 2 satisfies
    `ω^4 ≡ 1 (mod 5)` — `2 ∈ F_5` has order dividing `4 = 5 − 1`. -/
theorem Zp.smoke_teichmuller_5_pow4_trunc_one :
    (Zp.pow 5 (by decide)
      (Zp.teichmuller 5 (by decide)
        ⟨fun k => if k = 0 then ⟨2, by decide⟩ else ⟨0, by decide⟩⟩) 4).trunc 1
      = 1 :=
  Zp.teichmuller_pow_pred_trunc 5 (by decide) _ (by decide)
    E213.Lib.Math.NumberTheory.ModArith.UniversalFLT.prime_gcd_5 0

/-! ## Multiplicative decomposition `x = ω(x) · u`, `u ≡ 1 (mod p)`

The principal-unit cofactor `u(x) := ω(x)⁻¹ · x` is `≡ 1 (mod p)`,
because both `ω(x)` and `x` reduce to `x.digits 0` mod `p`, so their
ratio reduces to `1`.  Together with `teichmuller_pow_pred_trunc` this
gives the canonical split `ℤ_p^× ≃ μ_{p−1} × (1 + p·ℤ_p)`. -/

/-- The principal-unit cofactor `u(x) = ω(x)⁻¹ · x`.  Requires `x` a
    unit so that `ω(x)` (same digit-0) is invertible. -/
def Zp.teichmullerCofactor (p : Nat) (hp : 1 < p) (x : ZpSeq p)
    (h_gcd : (E213.Lib.Math.NumberTheory.ModArith.ModBezout.modBezout
              (x.digits 0).val p).1 = 1) : ZpSeq p :=
  Zp.mul p (Nat.lt_of_succ_lt hp)
    (Zp.invFull p (Nat.lt_of_succ_lt hp) (Zp.teichmuller p hp x) h_gcd) x

/-- **Principal-unit property**: `u(x) ≡ 1 (mod p)`, i.e.
    `(ω⁻¹ · x).trunc 1 = 1`.  The cofactor lands in `1 + p·ℤ_p`. -/
theorem Zp.teichmullerCofactor_trunc_one (p : Nat) (hp : 1 < p) (x : ZpSeq p)
    (h_gcd : (E213.Lib.Math.NumberTheory.ModArith.ModBezout.modBezout
              (x.digits 0).val p).1 = 1) :
    (Zp.teichmullerCofactor p hp x h_gcd).trunc 1 = 1 := by
  have hp' : 0 < p := Nat.lt_of_succ_lt hp
  -- u = ω⁻¹ · x.  Since ω.digits 0 = x.digits 0, x.trunc 1 = ω.trunc 1, so
  -- (ω⁻¹ · x).trunc 1 = (ω⁻¹ · ω).trunc 1 = (ω · ω⁻¹).trunc 1 = 1.
  show (Zp.mul p hp'
          (Zp.invFull p hp' (Zp.teichmuller p hp x) h_gcd) x).trunc 1 = 1
  have hx : x.trunc 1 = (Zp.teichmuller p hp x).trunc 1 :=
    (Zp.teichmuller_trunc_one p hp x).symm
  rw [Zp.mul_trunc p hp' (Zp.invFull p hp' (Zp.teichmuller p hp x) h_gcd) x 1, hx,
      ← Zp.mul_trunc p hp' (Zp.invFull p hp' (Zp.teichmuller p hp x) h_gcd)
        (Zp.teichmuller p hp x) 1,
      Zp.mul_trunc_comm p hp' (Zp.invFull p hp' (Zp.teichmuller p hp x) h_gcd)
        (Zp.teichmuller p hp x) 1]
  -- Goal: (ω · ω⁻¹).trunc 1 = 1.
  exact Zp.mul_invFull_correct p hp (Zp.teichmuller p hp x) h_gcd 0

/-- Smoke: the 5-adic cofactor of digit-0 = 2 is principal: `u ≡ 1 (mod 5)`. -/
theorem Zp.smoke_teichmullerCofactor_5_trunc_one
    (h_gcd : (E213.Lib.Math.NumberTheory.ModArith.ModBezout.modBezout 2 5).1 = 1) :
    (Zp.teichmullerCofactor 5 (by decide)
      ⟨fun k => if k = 0 then ⟨2, by decide⟩ else ⟨0, by decide⟩⟩ h_gcd).trunc 1
      = 1 :=
  Zp.teichmullerCofactor_trunc_one 5 (by decide) _ h_gcd

end E213.Lib.Math.NumberSystems.Padic
