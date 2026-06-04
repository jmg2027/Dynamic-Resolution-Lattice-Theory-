import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.FreshmanDream
/-!
# FLT primary form: `a^p ≡ a (mod p)` for prime p

The first formulation of Fermat's Little Theorem, by induction on `a`
using the freshman's dream `(a+1)^p ≡ a^p + 1 (mod p)`.

  · Base `a = 0`:  `0^p = 0 ≡ 0 (mod p)` for `p ≥ 1`.
  · Step `a = b + 1`:
      `(b + 1)^p mod p`
        = `(b^p + 1) mod p`           [freshman's dream]
        = `(b + 1) mod p`             [IH: `b^p ≡ b mod p`]

Conditional on the freshman's dream hypothesis (middle-binomial
vanishing mod p), which holds for primes p and is decidable per
prime.

All declarations PURE.
-/

namespace E213.Lib.Math.NumberTheory.DyadicFSM.FLT.FLTPrimary

open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Binomial (choose)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.FreshmanDream (freshman_dream)
open E213.Meta.Nat.AddMod213 (add_mod_gen)

/-- Helper: `0^(p' + 1) = 0`.  PURE (Nat.pow def + Nat.zero_mul). -/
private theorem zero_pow_succ (p' : Nat) : (0 : Nat)^(p' + 1) = 0 := by
  -- 0^(p'+1) = 0^p' * 0 = 0 by Nat.pow def + Nat.mul_zero
  show (0 : Nat)^p' * 0 = 0
  exact Nat.mul_zero _

/-- ★★★★★ **FLT primary form**:  `a^p ≡ a (mod p)` for prime `p`.

    Parameterised as `p = p' + 1` with `1 ≤ p'` (so `p ≥ 2`).
    Conditional on the middle-binomial vanishing hypothesis
    (`h_middle`), which captures primality of `p` algebraically.

    By induction on `a`:
      · base `a = 0`: `0^p = 0 ≡ 0`.
      · step `a = b + 1`: freshman's dream + IH.

    PURE. -/
theorem flt_primary (p' : Nat) (hp' : 1 ≤ p')
    (h_middle : ∀ k, k < p' →
      (choose (p' + 1) (k + 1)) % (p' + 1) = 0) :
    ∀ a, (a^(p' + 1)) % (p' + 1) = a % (p' + 1)
  | 0 => by
    show (0 : Nat)^(p' + 1) % (p' + 1) = 0 % (p' + 1)
    rw [zero_pow_succ]
  | b + 1 => by
    -- IH: b^p mod p = b mod p
    have ih : (b^(p' + 1)) % (p' + 1) = b % (p' + 1) :=
      flt_primary p' hp' h_middle b
    -- Apply freshman's dream: (b+1)^p ≡ b^p + 1 mod p
    have hfd : ((b + 1)^(p' + 1)) % (p' + 1) = (b^(p' + 1) + 1) % (p' + 1) :=
      freshman_dream b p' hp' h_middle
    rw [hfd]
    -- Goal: (b^(p'+1) + 1) % (p'+1) = (b + 1) % (p'+1)
    -- Apply add_mod_gen forward then IH then backward
    rw [add_mod_gen (b^(p' + 1)) 1 (p' + 1),
        ih,
        ← add_mod_gen b 1 (p' + 1)]

/-! ## Per-prime smokes -/

/-- FLT primary at p = 5: `∀ a, a^5 ≡ a (mod 5)`. -/
theorem flt_primary_5 (a : Nat) : (a^5) % 5 = a % 5 :=
  flt_primary 4 (by decide)
    E213.Lib.Math.NumberTheory.DyadicFSM.FLT.FreshmanDream.middle_vanish_5 a

/-- FLT primary at p = 7: `∀ a, a^7 ≡ a (mod 7)`. -/
theorem flt_primary_7 (a : Nat) : (a^7) % 7 = a % 7 :=
  flt_primary 6 (by decide)
    E213.Lib.Math.NumberTheory.DyadicFSM.FLT.FreshmanDream.middle_vanish_7 a

/-- Smoke at p = 5, a = 3: 3^5 = 243 = 48·5 + 3, so 3^5 ≡ 3 mod 5. -/
theorem flt_primary_5_at_3 : (3^5) % 5 = 3 % 5 := flt_primary_5 3

/-- Smoke at p = 7, a = 4: 4^7 = 16384 = 2340·7 + 4, so 4^7 ≡ 4 mod 7. -/
theorem flt_primary_7_at_4 : (4^7) % 7 = 4 % 7 := flt_primary_7 4

end E213.Lib.Math.NumberTheory.DyadicFSM.FLT.FLTPrimary
