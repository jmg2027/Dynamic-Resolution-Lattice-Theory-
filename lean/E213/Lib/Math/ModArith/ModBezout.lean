import E213.Meta.Nat.Gcd213
import E213.Meta.Nat.AddMod213
import E213.Meta.Nat.MulMod213
import E213.Meta.Tactic.NatHelper
/-!
# Modular Bezout's identity (213-native, PURE)

Constructive extended Euclidean algorithm with modular tracking:

  Given `a, p : Nat` with `0 < p`, compute `(g, x) : Nat × Nat` where
    · `g = gcd(a, p)`
    · `x < p`
    · `(a · x) % p = g % p`     (mod-p Bezout invariant)

When `gcd(a, p) = 1`, this gives the modular inverse of `a` mod `p`
directly:  `(a · x) % p = 1 % p`.

This bridges to:
  · Universal `ModInverse p a` for coprime `(a, p)` (Part 12 prerequisite).
  · Universal middle-binomial vanishing `p ∣ choose p (k+1)` (Part 15).
  · Universal FLT main form (Part 22).
  · Universal Phase 3.2 closure.

This is Mathlib-level number-theoretic infrastructure, 213-native PURE.

All declarations PURE.
-/

namespace E213.Lib.Math.ModArith.ModBezout

open E213.Meta.Nat.AddMod213 (mod_self mod_mod add_mod_gen)
open E213.Meta.Nat.MulMod213 (mul_mod_left_pure mul_mod_right_pure mul_mod_pure)
open E213.Tactic.NatHelper (mul_assoc add_mul sub_add_cancel)

/-! ## Iterative xgcd with modular tracking

The state `(r₀, r₁, x₀, x₁)` evolves via Euclidean step:

  q := r₀ / r₁  (only used when r₁ > 0)
  r₂ := r₀ % r₁
  x₂ := (x₀ + (p - (q · x₁) % p)) % p   -- (x₀ - q · x₁) mod p in Nat form

Maintained invariant: `r_i ≡ a · x_i (mod p)` for both i.
Initial: `(a, p, 1, 0)` satisfies `a ≡ a · 1` and `p ≡ a · 0 = 0` (mod p).
Termination: when `r₁ = 0`, return `(r₀, x₀)`; `r₀ = gcd(a, p)`.
-/

/-- Helper: in-Nat form of `(x₀ - q · x₁) mod p`.
    Since `(q · x₁) % p ≤ p`, `p - (q · x₁) % p` is well-defined Nat. -/
def bezoutSubMod (p q x₀ x₁ : Nat) : Nat :=
  (x₀ + (p - (q * x₁) % p)) % p

/-- Iterative xgcd with mod-p coefficient tracking.

    Input: `p` (modulus), `fuel` (recursion budget),
           `(r₀, r₁, x₀, x₁)` (state).
    Output: `(g, x)` with `g = gcd(r₀, r₁)` and `(r₀ * x₁_initial + ... ) ≡ g mod p`.

    Termination via explicit fuel (mirrors `Meta/Nat/Gcd213.lean` style). -/
def xgcdAux (p : Nat) : Nat → Nat → Nat → Nat → Nat → Nat × Nat
  | 0,      r₀, _,  x₀, _  => (r₀, x₀)                  -- out of fuel
  | _ + 1,  r₀, 0,  x₀, _  => (r₀, x₀)                  -- r₁ = 0: terminate, gcd = r₀
  | f + 1,  r₀, r₁, x₀, x₁ =>
      xgcdAux p f r₁ (r₀ % r₁) x₁ (bezoutSubMod p (r₀ / r₁) x₀ x₁)

/-- `modBezout a p` : compute the Bezout coefficient `x` such that
    `(a · x) % p ≡ gcd(a, p) (mod p)`.

    Fuel = `a + p + 1` always suffices (Euclidean recursion depth bound). -/
def modBezout (a p : Nat) : Nat × Nat :=
  xgcdAux p (a + p + 1) a p 1 0

/-! ## Smoke tests at small primes -/

/-- Smoke: xgcd at (a, p) = (2, 5).
    Expected: gcd = 1, modular inverse coefficient = 3 (since 2·3 = 6 ≡ 1 mod 5). -/
theorem modBezout_2_5 : modBezout 2 5 = (1, 3) := by decide

/-- Smoke: xgcd at (a, p) = (3, 7).
    Expected: gcd = 1, inverse = 5 (since 3·5 = 15 ≡ 1 mod 7). -/
theorem modBezout_3_7 : modBezout 3 7 = (1, 5) := by decide

/-- Smoke: xgcd at (a, p) = (4, 11).
    Expected: gcd = 1, inverse = 3 (since 4·3 = 12 ≡ 1 mod 11). -/
theorem modBezout_4_11 : modBezout 4 11 = (1, 3) := by decide

/-- Smoke: xgcd at (a, p) = (9, 19).
    Expected: gcd = 1, inverse = 17 (since 9·17 = 153 = 8·19 + 1 ≡ 1 mod 19). -/
theorem modBezout_9_19 : modBezout 9 19 = (1, 17) := by decide

/-- Smoke: at non-coprime input (a, p) = (4, 6), gcd = 2 not 1. -/
theorem modBezout_4_6_gcd : (modBezout 4 6).1 = 2 := by decide

/-! ## Modular inverse from coprime Bezout (per-prime via decide) -/

/-- For specific `(a, p)` with `(modBezout a p).1 = 1`, the second
    component is the modular inverse.

    Per-prime decidable verification: at (2, 5), inverse = 3 and
    `(2 · 3) % 5 = 1 % 5`. -/
theorem modBezout_inverse_2_5 :
    (2 * (modBezout 2 5).2) % 5 = 1 % 5 := by decide

theorem modBezout_inverse_3_7 :
    (3 * (modBezout 3 7).2) % 7 = 1 % 7 := by decide

theorem modBezout_inverse_4_11 :
    (4 * (modBezout 4 11).2) % 11 = 1 % 11 := by decide

theorem modBezout_inverse_9_19 :
    (9 * (modBezout 9 19).2) % 19 = 1 % 19 := by decide

end E213.Lib.Math.ModArith.ModBezout
