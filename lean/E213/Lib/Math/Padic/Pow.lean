import E213.Lib.Math.Padic.Foundation
import E213.Lib.Math.Padic.Arith
import E213.Lib.Math.ModArith.UniversalFLT
import E213.Meta.Tactic.NatHelper
import E213.Meta.Nat.AddMod213
import E213.Meta.Nat.MulMod213
/-!
# Real213-p-adic — natural-number power

`Zp.pow x n` is defined recursively via `Zp.mul`:
- `Zp.pow x 0 = ZpSeq.one`
- `Zp.pow x (n+1) = Zp.mul (Zp.pow x n) x`

The key compatibility theorem is `Zp.pow_trunc`:
`(Zp.pow x n).trunc m = (x.trunc m)^n % p^m`,
expressing trunc as a ring homomorphism from `ZpSeq` to `ℤ/p^m`.

This is foundational for Teichmüller lifts and other multiplicative
structures on `ℤ_p`.
-/

namespace E213.Lib.Math.Padic

/-- Natural-number power on `ZpSeq`.  Defined recursively as
    repeated multiplication. -/
def Zp.pow (p : Nat) (hp : 1 < p) (x : ZpSeq p) : Nat → ZpSeq p
  | 0 => ZpSeq.one p hp
  | n + 1 => Zp.mul p (Nat.lt_of_succ_lt hp) (Zp.pow p hp x n) x

/-- `Zp.pow x 0 = 1`. -/
theorem Zp.pow_zero (p : Nat) (hp : 1 < p) (x : ZpSeq p) :
    Zp.pow p hp x 0 = ZpSeq.one p hp := rfl

/-- `Zp.pow x (n + 1) = Zp.pow x n · x`. -/
theorem Zp.pow_succ_def (p : Nat) (hp : 1 < p) (x : ZpSeq p) (n : Nat) :
    Zp.pow p hp x (n + 1)
      = Zp.mul p (Nat.lt_of_succ_lt hp) (Zp.pow p hp x n) x := rfl

/-! ## Trunc compatibility -/

/-- `(ZpSeq.one).trunc m = 1 % p^m` — at m = 0 it's 0, otherwise 1. -/
private theorem one_trunc_form (p : Nat) (hp : 1 < p) :
    ∀ m, (ZpSeq.one p hp).trunc m = 1 % p^m
  | 0 => by
    show (0 : Nat) = 1 % p^0
    rw [Nat.pow_zero]
  | m + 1 => by
    rw [ZpSeq.trunc_one_succ p hp m]
    have h_lt : 1 < p^(m + 1) := by
      induction m with
      | zero => rw [Nat.pow_one]; exact hp
      | succ k ih =>
        have hp' : 0 < p := Nat.lt_of_succ_lt hp
        calc 1 < p^(k + 1) := ih
          _ ≤ p^(k + 1) * p := Nat.le_mul_of_pos_right _ hp'
          _ = p^(k + 2) := (Nat.pow_succ p (k + 1)).symm
    exact (Nat.mod_eq_of_lt h_lt).symm

/-- **Trunc compatibility**: `(Zp.pow x n).trunc m = (x.trunc m)^n % p^m`.
    Proved by induction on `n`. -/
theorem Zp.pow_trunc (p : Nat) (hp : 1 < p) (x : ZpSeq p) (m : Nat) :
    ∀ n, (Zp.pow p hp x n).trunc m = (x.trunc m)^n % p^m
  | 0 => by
    show (ZpSeq.one p hp).trunc m = (x.trunc m)^0 % p^m
    rw [one_trunc_form p hp m, Nat.pow_zero]
  | n + 1 => by
    rw [Zp.pow_succ_def]
    rw [Zp.mul_trunc p (Nat.lt_of_succ_lt hp) (Zp.pow p hp x n) x m]
    rw [Zp.pow_trunc p hp x m n]
    -- LHS: ((x.trunc m)^n % p^m * x.trunc m) % p^m
    -- RHS: (x.trunc m)^(n+1) % p^m
    rw [← E213.Meta.Nat.MulMod213.mul_mod_left_pure
          ((x.trunc m)^n) (x.trunc m) (p^m)]
    -- LHS: ((x.trunc m)^n * x.trunc m) % p^m
    rw [Nat.pow_succ (x.trunc m) n]

/-! ## Useful identities -/

/-- PURE: `a^m * a^n = a^(m+n)` by induction. -/
private theorem pow_add_pure_local (a : Nat) :
    ∀ m n, a^m * a^n = a^(m + n)
  | _, 0 => by rw [Nat.add_zero, Nat.pow_zero, Nat.mul_one]
  | m, n + 1 => by
    rw [Nat.pow_succ, ← E213.Tactic.NatHelper.mul_assoc,
        pow_add_pure_local a m n]
    show a^(m + n) * a = a^(m + (n + 1))
    rw [← Nat.add_assoc, ← Nat.pow_succ]

/-- `Zp.pow x 2 = Zp.mul (Zp.mul one x) x`.  Note this isn't `Zp.mul x x`
    directly because `pow` does `pow 0 = one`, then `pow 1 = one · x`,
    then `pow 2 = (one · x) · x`. -/
theorem Zp.pow_two_def (p : Nat) (hp : 1 < p) (x : ZpSeq p) :
    Zp.pow p hp x 2
      = Zp.mul p (Nat.lt_of_succ_lt hp)
          (Zp.mul p (Nat.lt_of_succ_lt hp) (ZpSeq.one p hp) x) x := rfl

/-- `(Zp.pow x 2).trunc m = (x.trunc m)² % p^m`. -/
theorem Zp.pow_two_trunc (p : Nat) (hp : 1 < p) (x : ZpSeq p) (m : Nat) :
    (Zp.pow p hp x 2).trunc m = (x.trunc m * x.trunc m) % p^m := by
  rw [Zp.pow_trunc p hp x m 2]
  show (x.trunc m)^2 % p^m = (x.trunc m * x.trunc m) % p^m
  rw [show (x.trunc m)^2 = x.trunc m * x.trunc m by
        rw [Nat.pow_succ, Nat.pow_one]]

/-- **Multiplicative homomorphism at trunc**:
    `(Zp.pow x (m + n)).trunc k = (Zp.pow x m · Zp.pow x n).trunc k`. -/
theorem Zp.pow_add_trunc (p : Nat) (hp : 1 < p) (x : ZpSeq p) (k m n : Nat) :
    (Zp.pow p hp x (m + n)).trunc k
      = (Zp.mul p (Nat.lt_of_succ_lt hp) (Zp.pow p hp x m) (Zp.pow p hp x n)).trunc k := by
  rw [Zp.mul_trunc p (Nat.lt_of_succ_lt hp) _ _ k]
  rw [Zp.pow_trunc p hp x k (m + n), Zp.pow_trunc p hp x k m,
      Zp.pow_trunc p hp x k n]
  -- Goal: (x.trunc k)^(m+n) % p^k = ((x.trunc k)^m % p^k * ((x.trunc k)^n % p^k)) % p^k
  rw [← pow_add_pure_local (x.trunc k) m n]
  -- Goal: ((x.trunc k)^m * (x.trunc k)^n) % p^k
  --     = ((x.trunc k)^m % p^k * ((x.trunc k)^n % p^k)) % p^k
  exact E213.Meta.Nat.MulMod213.mul_mod_pure _ _ _

/-- PURE: `a^p = a^(p - 1) * a` for `0 < p`. -/
private theorem pow_pred_eq (a p : Nat) (hp : 0 < p) :
    a^p = a^(p - 1) * a := by
  cases p with
  | zero => exact absurd hp (Nat.lt_irrefl 0)
  | succ k =>
    show a^(k + 1) = a^(k + 1 - 1) * a
    rw [show k + 1 - 1 = k from rfl]
    exact Nat.pow_succ a k

/-! ## Fermat's little theorem on `ZpSeq`

For p prime, `x^p ≡ x (mod p)` for any `x : ZpSeq p`.  This is the
first-digit case of the Teichmüller convergence: iterating `x ↦ x^p`
fixes the digit-0 mod p.
-/

/-- **Fermat's lift to digit-0**: for `p` prime (encoded as
    `prime_gcd p`), `(Zp.pow x p).trunc 1 = x.trunc 1`.

    Proof: `(x^p).trunc 1 = (x.trunc 1)^p % p`.  By Fermat
    (`universal_flt_main`), `a^(p-1) ≡ 1 (mod p)`, so `a^p ≡ a (mod p)`.
    Since `x.trunc 1 < p`, the mod is trivial. -/
theorem Zp.pow_p_trunc_one (p : Nat) (hp : 1 < p) (x : ZpSeq p)
    (h_prime_gcd : ∀ m, 0 < m
                  → m < p
                  → (E213.Lib.Math.ModArith.ModBezout.modBezout m p).1 = 1) :
    (Zp.pow p hp x p).trunc 1 = x.trunc 1 := by
  have hp' : 0 < p := Nat.lt_of_succ_lt hp
  rw [Zp.pow_trunc p hp x 1 p, Nat.pow_one]
  -- Goal: (x.trunc 1)^p % p = x.trunc 1
  -- x.trunc 1 < p^1 = p.
  have h_lt : x.trunc 1 < p := by
    have h := ZpSeq.trunc_lt_p_pow hp' x 1
    rw [Nat.pow_one] at h
    exact h
  -- Case on whether x.trunc 1 = 0.
  cases h_case : Nat.decEq (x.trunc 1) 0 with
  | isTrue h_zero =>
    rw [h_zero]
    -- 0^p % p = 0.  p > 0 so p ≥ 1, so 0^p = 0 when p ≥ 1.  For p = 1
    -- (excluded by 1 < p), 0^0 = 1.  Here p > 1 so p ≥ 2, 0^p = 0.
    have : (0 : Nat)^p = 0 := by
      cases p with
      | zero => exact absurd hp (Nat.not_lt_zero 1)
      | succ q => show (0 : Nat)^(q + 1) = 0; rw [Nat.pow_succ, Nat.mul_zero]
    rw [this, E213.Tactic.NatHelper.zero_mod]
  | isFalse h_ne =>
    have h_pos : 0 < x.trunc 1 := Nat.pos_of_ne_zero h_ne
    rw [pow_pred_eq (x.trunc 1) p hp']
    -- Goal: ((x.trunc 1)^(p-1) * x.trunc 1) % p = x.trunc 1
    -- Apply mul_mod_left_pure to reduce the first factor mod p.
    rw [E213.Meta.Nat.MulMod213.mul_mod_left_pure
          ((x.trunc 1)^(p - 1)) (x.trunc 1) p]
    -- Goal: (((x.trunc 1)^(p-1) % p) * x.trunc 1) % p = x.trunc 1
    rw [E213.Lib.Math.ModArith.UniversalFLT.universal_flt_main
          (x.trunc 1) p hp h_pos h_lt h_prime_gcd]
    -- Goal: ((1 % p) * x.trunc 1) % p = x.trunc 1
    rw [Nat.mod_eq_of_lt hp, Nat.one_mul]
    exact Nat.mod_eq_of_lt h_lt

/-- Smoke: `2^5 ≡ 2 (mod 5)` in `ℤ_5`.  Build an `x` with digit-0 = 2
    and verify Fermat at the digit level. -/
theorem Zp.smoke_pow_5_digit_two :
    (Zp.pow 5 (by decide)
      ⟨fun k => if k = 0 then ⟨2, by decide⟩ else ⟨0, by decide⟩⟩ 5).trunc 1
      = 2 := by
  rw [Zp.pow_p_trunc_one 5 (by decide) _
        E213.Lib.Math.ModArith.UniversalFLT.prime_gcd_5]
  -- (x.trunc 1) where x.digits 0 = 2.
  rfl

end E213.Lib.Math.Padic
