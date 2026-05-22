import E213.Meta.Nat.MulMod213
import E213.Meta.Nat.AddMod213
/-!
# 213-native `modPow` and basic identities — FLT prerequisites

`modPow p a k = a^k % p` with PURE basic identities:
  · `modPow p a 0 = 1 % p`
  · `modPow p a (k+1) = (modPow p a k * a) % p`
  · `modPow_add`: `modPow p a (m+n) = (modPow p a m * modPow p a n) % p`
  · `modPow_one`: `modPow p a 1 = a % p`
  · `modPow_mul`: `modPow p a (m*n) = modPow p (modPow p a m) n`
-/

namespace E213.Meta.Nat.ModPow213

open E213.Meta.Nat.MulMod213 (mul_mod_left_pure mul_mod_right_pure mul_mod_pure)
open E213.Meta.Nat.AddMod213 (mod_mod)
open E213.Tactic.NatHelper (mul_assoc)

/-- `a^k mod p`.  Recursively defined. -/
def modPow (p a : Nat) : Nat → Nat
  | 0 => 1 % p
  | k+1 => (modPow p a k * a) % p

/-- `modPow p a 0 = 1 % p`.  Definitional. -/
theorem modPow_zero (p a : Nat) : modPow p a 0 = 1 % p := rfl

/-- `modPow p a (k+1) = (modPow p a k * a) % p`.  Definitional. -/
theorem modPow_succ (p a k : Nat) :
    modPow p a (k + 1) = (modPow p a k * a) % p := rfl

/-- `modPow p a 1 = a % p`. -/
theorem modPow_one (p a : Nat) : modPow p a 1 = a % p := by
  show ((1 % p) * a) % p = a % p
  rw [← mul_mod_left_pure 1 a p]
  rw [Nat.one_mul]

/-- `modPow` is mod-invariant in the base: `modPow p (a % p) k = modPow p a k`. -/
theorem modPow_mod_left (p a k : Nat) :
    modPow p (a % p) k = modPow p a k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    show (modPow p (a % p) k * (a % p)) % p = (modPow p a k * a) % p
    rw [ih]
    rw [← mul_mod_right_pure (modPow p a k) a p]

/-- `modPow p a k` is always `< p` (when 0 < p). -/
theorem modPow_lt (p a : Nat) (hp : 0 < p) (k : Nat) : modPow p a k < p := by
  induction k with
  | zero => exact Nat.mod_lt _ hp
  | succ _ _ => exact Nat.mod_lt _ hp

/-- `modPow p a (m + n) = (modPow p a m * modPow p a n) % p`.  PURE. -/
theorem modPow_add (p a : Nat) (hp : 0 < p) (m n : Nat) :
    modPow p a (m + n) = (modPow p a m * modPow p a n) % p := by
  induction n with
  | zero =>
    show modPow p a m = (modPow p a m * (1 % p)) % p
    rw [← mul_mod_right_pure (modPow p a m) 1 p]
    rw [Nat.mul_one]
    rw [Nat.mod_eq_of_lt (modPow_lt p a hp m)]
  | succ n ih =>
    show modPow p a (m + (n + 1)) = (modPow p a m * modPow p a (n + 1)) % p
    show (modPow p a (m + n) * a) % p
      = (modPow p a m * ((modPow p a n * a) % p)) % p
    rw [ih]
    -- Goal: ((modPow p a m * modPow p a n) % p * a) % p
    --     = (modPow p a m * ((modPow p a n * a) % p)) % p
    rw [← mul_mod_left_pure (modPow p a m * modPow p a n) a p]
    rw [← mul_mod_right_pure (modPow p a m) (modPow p a n * a) p]
    -- Goal: (modPow p a m * modPow p a n * a) % p
    --     = (modPow p a m * (modPow p a n * a)) % p
    rw [mul_assoc]

/-- `modPow p a (m * n) = modPow p (modPow p a m) n`.  PURE. -/
theorem modPow_mul (p a : Nat) (hp : 0 < p) (m n : Nat) :
    modPow p a (m * n) = modPow p (modPow p a m) n := by
  induction n with
  | zero =>
    show modPow p a (m * 0) = modPow p (modPow p a m) 0
    rw [Nat.mul_zero]
    rfl
  | succ n ih =>
    show modPow p a (m * (n + 1)) = modPow p (modPow p a m) (n + 1)
    show modPow p a (m * (n + 1)) = (modPow p (modPow p a m) n * modPow p a m) % p
    rw [Nat.mul_succ]
    rw [modPow_add p a hp (m * n) m]
    rw [ih]

end E213.Meta.Nat.ModPow213
