import E213.Meta.Nat.AddMod213
import E213.Meta.Nat.MulMod213
import E213.Meta.Tactic.NatHelper
/-!
# Golden ratio mod p — G119 Phase 3.2 algebraic foundation

For odd `p > 1` and `s : Nat` with `s² ≡ 5 (mod p)`, define

  `inv2 p := p / 2 + 1`                — multiplicative inverse of 2 mod p
  `phi p s := ((1 + s) * inv2 p) % p`  — golden ratio mod p

and prove:

  · `two_mul_inv2`     :  `2 * inv2 p ≡ 1  (mod p)`
  · `two_mul_phi_eq`   :  `2 * phi p s ≡ 1 + s  (mod p)`     (bridge)
  · `four_phi_sq_eq`   :  `4 * phi² ≡ (1+s)² ≡ 1 + 2s + 5 = 6 + 2s  (mod p)`,
                          using `s² ≡ 5`
  · `four_phi_plus_one_eq` : `4 * (phi + 1) ≡ 6 + 2s  (mod p)`
  · **`four_phi_sq_eq_four_phi_plus_one`** :
                          `4 * phi² ≡ 4 * (phi + 1)  (mod p)`,
                          the **scaled** form of `phi² = phi + 1`

The unscaled identity `phi² ≡ phi + 1  (mod p)` follows from
multiplicative cancellation of 4 mod p (i.e., `gcd(4, p) = 1` for
odd p, equivalent to existence of `4⁻¹ mod p`).  That cancellation
requires either explicit `4⁻¹` (Bézout / xgcd) or the multiplicative
order theory of `(Fin p)*` — both are G119 Phase 2.1 prerequisites
that remain multi-session.

This file is **algebra only** — no FLT, no QR existence claim.
Caller provides `s` with `s² ≡ 5 mod p`; we verify the scaled φ
recurrence.

All declarations PURE.
-/

namespace E213.Lib.Math.DyadicFSM.PhiMod5

open E213.Meta.Nat.AddMod213 (add_mod_gen mod_mod mod_self div_add_mod)
open E213.Meta.Nat.MulMod213 (mul_mod_left_pure mul_mod_right_pure mul_mod_pure)
open E213.Tactic.NatHelper (mul_assoc add_mul)

/-- `inv2 p := p / 2 + 1`.  For odd `p > 1`, this is the
    multiplicative inverse of 2 mod p (see `two_mul_inv2`). -/
def inv2 (p : Nat) : Nat := p / 2 + 1

/-- ★ `2 * inv2 p ≡ 1 (mod p)` for odd `p > 1`.  PURE.
    The `1 < p` hypothesis is structural (would be required by any
    nontrivial consumer); the proof uses only `p % 2 = 1`. -/
theorem two_mul_inv2 (p : Nat) (_hp : 1 < p) (hpo : p % 2 = 1) :
    (2 * inv2 p) % p = 1 % p := by
  show (2 * (p / 2 + 1)) % p = 1 % p
  rw [Nat.mul_add, Nat.mul_one]
  -- Goal: (2 * (p / 2) + 2) % p = 1 % p
  have hdiv : 2 * (p / 2) + p % 2 = p := div_add_mod p 2
  rw [hpo] at hdiv
  -- hdiv : 2 * (p / 2) + 1 = p
  have hsucc : 2 * (p / 2) + 2 = (2 * (p / 2) + 1) + 1 := by
    rw [Nat.add_assoc]
  rw [hsucc, hdiv]
  -- Goal: (p + 1) % p = 1 % p
  rw [add_mod_gen p 1 p, mod_self, Nat.zero_add, mod_mod]

/-- `phi p s := ((1 + s) * inv2 p) % p` — golden ratio mod p,
    given a square root `s` of 5 mod p. -/
def phi (p s : Nat) : Nat := ((1 + s) * inv2 p) % p

/-- `phi p s < p` for `p > 0` (by construction as `_ % p`). -/
theorem phi_lt (p s : Nat) (hp : 0 < p) : phi p s < p :=
  Nat.mod_lt _ hp

/-- ★ **Bridge identity**: `2 * phi ≡ 1 + s (mod p)`.
    Uses `2 * inv2 ≡ 1`.  PURE. -/
theorem two_mul_phi_eq (p s : Nat) (hp : 1 < p) (hpo : p % 2 = 1) :
    (2 * phi p s) % p = (1 + s) % p := by
  -- phi p s = ((1 + s) * inv2 p) % p
  -- 2 * phi = 2 * (((1+s) * inv2) % p)
  -- (2 * phi) % p = (2 * ((1+s) * inv2)) % p = ((1+s) * (2 * inv2)) % p
  -- ≡ (1+s) * 1 mod p = 1+s mod p
  have step1 : (2 * phi p s) % p = (2 * ((1 + s) * inv2 p)) % p := by
    show (2 * (((1 + s) * inv2 p) % p)) % p = (2 * ((1 + s) * inv2 p)) % p
    exact (mul_mod_right_pure 2 ((1 + s) * inv2 p) p).symm
  have step2 : 2 * ((1 + s) * inv2 p) = (1 + s) * (2 * inv2 p) := by
    rw [← mul_assoc, Nat.mul_comm 2 (1 + s), mul_assoc]
  rw [step1, step2]
  -- Goal: ((1 + s) * (2 * inv2 p)) % p = (1 + s) % p
  -- Introduce inner mod on `2 * inv2 p`, substitute via two_mul_inv2:
  rw [mul_mod_right_pure (1 + s) (2 * inv2 p) p, two_mul_inv2 p hp hpo]
  -- Goal: ((1 + s) * (1 % p)) % p = (1 + s) % p
  -- Strip inner mod: (1+s) * (1%p) % p = (1+s) * 1 % p = (1+s) % p
  rw [← mul_mod_right_pure (1 + s) 1 p, Nat.mul_one]

/-- Helper: `4 * (a * a) = (2 * a) * (2 * a)` in Nat. -/
private theorem four_mul_sq (a : Nat) : 4 * (a * a) = (2 * a) * (2 * a) := by
  -- (2 * a) * (2 * a) = 2 * (a * (2 * a)) = 2 * (a * 2 * a)
  --                   = 2 * (2 * a * a) = 2 * 2 * (a * a) = 4 * (a * a)
  rw [mul_assoc 2 a (2 * a), ← mul_assoc a 2 a]
  rw [Nat.mul_comm a 2, mul_assoc 2 a a, ← mul_assoc 2 2 (a * a)]

/-- Helper: `(4 * (phi p s * phi p s)) % p = ((2 * phi p s) * (2 * phi p s)) % p`. -/
private theorem four_phi_sq (p s : Nat) :
    (4 * (phi p s * phi p s)) % p
      = ((2 * phi p s) * (2 * phi p s)) % p := by
  rw [four_mul_sq]

/-- ★ **Scaled phi² reduction**: `4 * phi² ≡ (1+s) * (1+s) (mod p)`.
    Uses the bridge `two_mul_phi_eq` + Nat algebra.  PURE. -/
theorem four_phi_sq_eq (p s : Nat) (hp : 1 < p) (hpo : p % 2 = 1) :
    (4 * (phi p s * phi p s)) % p = ((1 + s) * (1 + s)) % p := by
  rw [four_phi_sq p s]
  -- Goal: ((2 * phi p s) * (2 * phi p s)) % p = ((1 + s) * (1 + s)) % p
  rw [mul_mod_pure (2 * phi p s) (2 * phi p s) p]
  rw [two_mul_phi_eq p s hp hpo]
  rw [← mul_mod_pure (1 + s) (1 + s) p]

/-- Helper: expand `(1+s) * (1+s) = 1 + 2*s + s*s` in Nat. -/
private theorem expand_one_plus_s_sq (s : Nat) :
    (1 + s) * (1 + s) = 1 + 2 * s + s * s := by
  -- (1 + s) * (1 + s) = 1*(1+s) + s*(1+s) = (1 + s) + (s + s*s)
  rw [add_mul, Nat.one_mul]
  -- Goal: 1 + s + s * (1 + s) = 1 + 2 * s + s * s
  rw [Nat.mul_add, Nat.mul_one]
  -- Goal: 1 + s + (s + s * s) = 1 + 2 * s + s * s
  rw [← Nat.add_assoc (1 + s) s (s * s)]
  -- Goal: 1 + s + s + s * s = 1 + 2 * s + s * s
  rw [Nat.add_assoc 1 s s]
  -- Goal: 1 + (s + s) + s * s = 1 + 2 * s + s * s
  rw [← Nat.two_mul s]

/-- ★ **Expand & substitute**: `(1+s) * (1+s) ≡ 6 + 2s (mod p)`,
    using `s² ≡ 5 (mod p)`.  PURE. -/
theorem one_plus_s_sq_eq (p s : Nat) (hs2 : (s * s) % p = 5 % p) :
    ((1 + s) * (1 + s)) % p = (6 + 2 * s) % p := by
  rw [expand_one_plus_s_sq]
  -- Goal: (1 + 2*s + s*s) % p = (6 + 2 * s) % p
  rw [add_mod_gen (1 + 2 * s) (s * s) p, hs2,
      ← add_mod_gen (1 + 2 * s) 5 p]
  -- Goal: (1 + 2*s + 5) % p = (6 + 2 * s) % p
  -- 1 + 2*s + 5 = 6 + 2*s by rearrangement
  have heq : 1 + 2 * s + 5 = 6 + 2 * s := by
    rw [Nat.add_right_comm 1 (2 * s) 5]
  rw [heq]

/-- Helper: `4 * (phi + 1) = 2 * (2 * phi) + 4` in Nat. -/
private theorem four_phi_plus_one (p s : Nat) :
    4 * (phi p s + 1) = 2 * (2 * phi p s) + 4 := by
  rw [Nat.mul_add, Nat.mul_one]
  rw [← mul_assoc 2 2 (phi p s)]

/-- ★ **Scaled (phi + 1) reduction**: `4 * (phi + 1) ≡ 6 + 2s (mod p)`. -/
theorem four_phi_plus_one_eq (p s : Nat) (hp : 1 < p) (hpo : p % 2 = 1) :
    (4 * (phi p s + 1)) % p = (6 + 2 * s) % p := by
  rw [four_phi_plus_one]
  -- Goal: (2 * (2 * phi p s) + 4) % p = (6 + 2 * s) % p
  rw [add_mod_gen (2 * (2 * phi p s)) 4 p]
  rw [mul_mod_right_pure 2 (2 * phi p s) p]
  rw [two_mul_phi_eq p s hp hpo]
  rw [← mul_mod_right_pure 2 (1 + s) p]
  rw [← add_mod_gen (2 * (1 + s)) 4 p]
  -- Goal: (2 * (1 + s) + 4) % p = (6 + 2 * s) % p
  congr 1
  -- 2 * (1 + s) + 4 = 6 + 2 * s
  rw [Nat.mul_add, Nat.mul_one]
  -- 2 + 2 * s + 4 = 6 + 2 * s
  rw [Nat.add_right_comm 2 (2 * s) 4]

/-- ★★★ **Scaled φ recurrence** (G119 Phase 3.2 algebraic kernel):
    `4 * phi² ≡ 4 * (phi + 1)  (mod p)`,
    given `s² ≡ 5 (mod p)` and odd `p > 1`.

    The unscaled `phi² ≡ phi + 1 (mod p)` follows by multiplicative
    cancellation of 4 mod p (gcd(4, p) = 1 for odd p > 1).  That
    cancellation is G119 Phase 2.1 (FLT / xgcd) prerequisite work,
    multi-session.

    PURE. -/
theorem four_phi_sq_eq_four_phi_plus_one (p s : Nat)
    (hp : 1 < p) (hpo : p % 2 = 1) (hs2 : (s * s) % p = 5 % p) :
    (4 * (phi p s * phi p s)) % p = (4 * (phi p s + 1)) % p := by
  rw [four_phi_sq_eq p s hp hpo]
  rw [one_plus_s_sq_eq p s hs2]
  rw [← four_phi_plus_one_eq p s hp hpo]

/-! ## Smoke tests at split primes -/

/-- Smoke: at p=11, s=4 satisfies 4² ≡ 5 (mod 11). -/
theorem sqrt5_mod_11 : (4 * 4) % 11 = 5 % 11 := by decide

/-- Smoke: at p=11, the scaled φ identity is verifiable. -/
theorem phi_mod_11_scaled :
    (4 * (phi 11 4 * phi 11 4)) % 11 = (4 * (phi 11 4 + 1)) % 11 :=
  four_phi_sq_eq_four_phi_plus_one 11 4 (by decide) (by decide) sqrt5_mod_11

/-- Smoke: at p=19, s=9 satisfies 9² = 81 = 4·19 + 5 ≡ 5 (mod 19). -/
theorem sqrt5_mod_19 : (9 * 9) % 19 = 5 % 19 := by decide

/-- Smoke: at p=19, the scaled φ identity is verifiable. -/
theorem phi_mod_19_scaled :
    (4 * (phi 19 9 * phi 19 9)) % 19 = (4 * (phi 19 9 + 1)) % 19 :=
  four_phi_sq_eq_four_phi_plus_one 19 9 (by decide) (by decide) sqrt5_mod_19

end E213.Lib.Math.DyadicFSM.PhiMod5
