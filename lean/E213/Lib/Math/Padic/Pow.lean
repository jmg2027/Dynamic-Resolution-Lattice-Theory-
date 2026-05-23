import E213.Lib.Math.Padic.Foundation
import E213.Lib.Math.Padic.Arith
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

end E213.Lib.Math.Padic
