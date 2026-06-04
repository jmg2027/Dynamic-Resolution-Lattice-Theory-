import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Binomial
import E213.Meta.Nat.MulMod213
import E213.Meta.Nat.AddMod213
import E213.Lib.Math.NumberTheory.DyadicFSM.MulOrderPigeonhole
/-!
# Prime divisibility of binomial middle terms — FLT prerequisite

For prime `p` and `0 < k + 1 < p`:  `p ∣ choose p (k + 1)`.

Derivation chain:
  1. `choose_succ_mul (p - 1) k`:  `(k+1) · choose p (k+1) = p · choose (p-1) k`
     — Nat equation, so `(k+1) · choose p (k+1)` IS a multiple of `p`.
  2. mod `p`:  `((k+1) · choose p (k+1)) % p = 0`.
  3. Multiplicative inverse:  if `(k+1) · r ≡ 1 (mod p)` (explicit
     `ModInverse` witness), multiply both sides by `r`:
       `r · (k+1) · choose p (k+1) ≡ choose p (k+1) (mod p)`,
     and LHS ≡ 0, so `choose p (k+1) % p = 0`, i.e., `p ∣ choose p (k+1)`.

This module avoids full Euclid's-lemma / Bezout infrastructure by
requiring the caller to supply an explicit `ModInverse p (k+1)`
witness.  For prime `p` and `0 < k + 1 < p`, such a witness exists
(via Bezout, multi-session) — but for any specific prime, the
witness is decidable.

All declarations PURE.
-/

namespace E213.Lib.Math.NumberTheory.DyadicFSM.FLT.ChoosePrime

open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Binomial (choose choose_succ_mul)
open E213.Meta.Nat.MulMod213 (mul_mod_left_pure mul_mod_right_pure mul_mod_pure)
open E213.Meta.Nat.AddMod213 (mod_self)
open E213.Tactic.NatHelper (mul_assoc add_mul_mod_self_pure)
open E213.Lib.Math.NumberTheory.DyadicFSM.MulOrderPigeonhole (ModInverse)

/-- `(p * x) % p = 0` for any `x : Nat` and `0 < p`.  PURE replacement
    for `Nat.mul_mod_right`.  Proven via `add_mul_mod_self_pure` at
    `a = 0`, `c = x`. -/
theorem mul_p_mod_eq_zero (p x : Nat) : (p * x) % p = 0 := by
  -- (p * x) = (0 + x * p)  via comm
  rw [Nat.mul_comm p x]
  -- Goal: (x * p) % p = 0
  -- Use add_mul_mod_self_pure : (a + n * c) % c = a % c at a = 0
  -- (0 + x * p) % p = 0 % p = 0
  have h := add_mul_mod_self_pure 0 p x
  -- h : (0 + x * p) % p = 0 % p
  rw [Nat.zero_add] at h
  -- h : (x * p) % p = 0 % p
  rw [h]
  -- Goal: 0 % p = 0 (definitional)
  rfl

/-- ★ **Key step**: `((k+1) · choose p (k+1)) % p = 0` for `p ≥ 1`.

    From `choose_succ_mul (p-1) k` (which requires `p - 1 + 1 = p`,
    i.e., `p ≥ 1`):  the LHS `(k+1) · choose p (k+1)` equals
    `p · choose (p-1) k`, which is divisible by `p`.  PURE. -/
theorem key_mul_choose_mod (p k : Nat) (hp : 1 ≤ p) :
    ((k + 1) * choose p (k + 1)) % p = 0 := by
  -- Rewrite p as (p-1) + 1.  For p ≥ 1, (p-1) + 1 = p.
  match p, hp with
  | p' + 1, _ =>
    -- choose_succ_mul p' k : (k+1) * choose (p'+1) (k+1) = (p'+1) * choose p' k
    rw [choose_succ_mul p' k]
    -- Goal: ((p' + 1) * choose p' k) % (p' + 1) = 0
    exact mul_p_mod_eq_zero (p' + 1) (choose p' k)

/-- ★★★ **Prime divisibility of binomial middle term** (via explicit inverse):

    For `p > 1` and an explicit modular inverse `r` of `k + 1` mod `p`
    (i.e., `((k+1) * r) % p = 1 % p`):  `p ∣ choose p (k + 1)`,
    equivalently `(choose p (k + 1)) % p = 0`.

    PURE.  Combines `key_mul_choose_mod` (divisibility upgrade via
    `choose_succ_mul`) with the modular cancellation chain from the
    explicit inverse.

    For prime `p` and `0 < k + 1 < p`: `gcd(k+1, p) = 1`, so such an
    inverse exists (Bezout, multi-session); per-prime instances are
    decidable. -/
theorem choose_p_dvd_of_inverse (p k : Nat) (hp : 1 < p)
    (mi : ModInverse p (k + 1)) :
    (choose p (k + 1)) % p = 0 := by
  have hp_pos : 1 ≤ p := Nat.le_of_lt hp
  -- Key step: ((k+1) * choose p (k+1)) % p = 0
  have h_key := key_mul_choose_mod p k hp_pos
  -- Multiply both sides by r = mi.inv.
  -- (r * ((k+1) * choose p (k+1))) % p = (r * 0) % p = 0.
  have h_mult : (mi.inv * ((k + 1) * choose p (k + 1))) % p = 0 := by
    rw [mul_mod_right_pure mi.inv ((k + 1) * choose p (k + 1)) p, h_key]
    rw [Nat.mul_zero]
    rfl
  -- LHS rearrange: r * ((k+1) * X) = ((k+1) * r) * X
  --   via mul_assoc + mul_comm.
  have h_rearrange : mi.inv * ((k + 1) * choose p (k + 1))
                  = (k + 1) * mi.inv * choose p (k + 1) := by
    rw [← mul_assoc mi.inv (k + 1) (choose p (k + 1)),
        Nat.mul_comm mi.inv (k + 1)]
  rw [h_rearrange] at h_mult
  -- h_mult : ((k + 1) * mi.inv * choose p (k + 1)) % p = 0
  -- Pull (k+1)*mi.inv mod, substitute inv_eq, cancel:
  rw [mul_mod_left_pure ((k + 1) * mi.inv) (choose p (k + 1)) p,
      mi.inv_eq] at h_mult
  -- h_mult : ((1 % p) * choose p (k + 1)) % p = 0
  rw [← mul_mod_left_pure 1 (choose p (k + 1)) p, Nat.one_mul] at h_mult
  exact h_mult

/-! ## Per-prime smokes (decidable inverses) -/

/-- Smoke: at p=5, k=1: inverse of 2 mod 5 is 3 (since 2·3=6≡1 mod 5). -/
def modInv_2_mod_5 : ModInverse 5 2 :=
  { inv := 3, inv_lt := by decide, inv_eq := by decide }

/-- Smoke: `choose 5 2 = 10`, and `10 % 5 = 0`.  Derived via the
    bridge from `modInv_2_mod_5`. -/
theorem choose_5_2_mod_5 : (choose 5 2) % 5 = 0 :=
  choose_p_dvd_of_inverse 5 1 (by decide) modInv_2_mod_5

/-- Smoke: at p=7, k=2: inverse of 3 mod 7 is 5 (since 3·5=15≡1 mod 7). -/
def modInv_3_mod_7 : ModInverse 7 3 :=
  { inv := 5, inv_lt := by decide, inv_eq := by decide }

/-- Smoke: `choose 7 3 = 35`, and `35 % 7 = 0`. -/
theorem choose_7_3_mod_7 : (choose 7 3) % 7 = 0 :=
  choose_p_dvd_of_inverse 7 2 (by decide) modInv_3_mod_7

end E213.Lib.Math.NumberTheory.DyadicFSM.FLT.ChoosePrime
