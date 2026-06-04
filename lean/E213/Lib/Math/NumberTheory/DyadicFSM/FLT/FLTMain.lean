import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.FLTPrimary
import E213.Lib.Math.NumberTheory.DyadicFSM.MulOrderPigeonhole
/-!
# FLT main form: `a^(p - 1) ≡ 1 (mod p)` for `a` invertible mod p

The classical statement of Fermat's Little Theorem.  Derived from
the primary form `a^p ≡ a (mod p)` by multiplying both sides by an
explicit modular inverse `r` of `a`:

  `a * a^(p-1) ≡ a (mod p)`           [FLT primary, with p = p'+1]
  `r * (a * a^(p-1)) ≡ r * a (mod p)`  [multiply by r]
  `(r * a) * a^(p-1) ≡ r * a (mod p)`  [reassociate]
  `1 * a^(p-1) ≡ 1 (mod p)`            [substitute r * a ≡ 1]
  `a^(p-1) ≡ 1 (mod p)`                [Nat.one_mul]

Conditional on (1) the FLT primary form (which requires the middle-
binomial vanishing hypothesis from `freshman_dream`) and (2) an
explicit `ModInverse p a` (from Part 12, which Bezout provides for
prime p and a coprime to p; decidable per specific (p, a)).

All declarations PURE.
-/

namespace E213.Lib.Math.NumberTheory.DyadicFSM.FLT.FLTMain

open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Binomial (choose)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.FLTPrimary (flt_primary)
open E213.Lib.Math.NumberTheory.DyadicFSM.MulOrderPigeonhole (ModInverse)
open E213.Meta.Nat.MulMod213 (mul_mod_left_pure mul_mod_right_pure)
open E213.Tactic.NatHelper (mul_assoc)

/-- ★★★★★★ **Fermat's Little Theorem (main form)**:
    `a^(p - 1) ≡ 1 (mod p)` for `a` invertible mod `p`, where `p` is
    "prime" in the sense that the middle binomial coefficients vanish
    mod `p`.

    Parameterised as `p = p' + 1` with `1 ≤ p'`.  Conditional on:
      · `h_middle` — middle-binomial vanishing (captures primality)
      · `mi` — explicit `ModInverse (p' + 1) a` witness

    Both hypotheses are decidable per specific (p, a).  Universal
    forms require Bezout (multi-session).

    PURE. -/
theorem flt_main (a p' : Nat) (hp' : 1 ≤ p')
    (h_middle : ∀ k, k < p' →
      (choose (p' + 1) (k + 1)) % (p' + 1) = 0)
    (mi : ModInverse (p' + 1) a) :
    (a^p') % (p' + 1) = 1 % (p' + 1) := by
  -- Primary: (a^(p'+1)) % (p'+1) = a % (p'+1)
  have h_prim : (a^(p' + 1)) % (p' + 1) = a % (p' + 1) :=
    flt_primary p' hp' h_middle a
  -- a^(p'+1) = a^p' * a definitionally
  have h_pow : a^(p' + 1) = a^p' * a := rfl
  rw [h_pow] at h_prim
  -- h_prim : (a^p' * a) % (p'+1) = a % (p'+1)
  -- Multiply both sides by mi.inv:
  -- (mi.inv * (a^p' * a)) % (p'+1) = (mi.inv * a) % (p'+1)
  have h_mult : (mi.inv * (a^p' * a)) % (p' + 1)
              = (mi.inv * a) % (p' + 1) := by
    rw [mul_mod_right_pure mi.inv (a^p' * a) (p' + 1),
        h_prim,
        ← mul_mod_right_pure mi.inv a (p' + 1)]
  -- LHS reduction:
  --   (mi.inv * (a^p' * a)) % (p'+1)
  -- = ((mi.inv * a^p') * a) % (p'+1)       [← mul_assoc]
  -- = ((a^p' * mi.inv) * a) % (p'+1)       [mul_comm]
  -- = (a^p' * (mi.inv * a)) % (p'+1)       [mul_assoc]
  -- = (a^p' * ((mi.inv * a) % (p'+1))) % (p'+1)  [mul_mod_right_pure backward]
  -- = (a^p' * ((a * mi.inv) % (p'+1))) % (p'+1)  [Nat.mul_comm on a, mi.inv]
  -- = (a^p' * (1 % (p'+1))) % (p'+1)       [substitute mi.inv_eq]
  -- = (a^p' * 1) % (p'+1)                 [mul_mod_right_pure forward]
  -- = (a^p') % (p'+1)                     [Nat.mul_one]
  have h_lhs : (mi.inv * (a^p' * a)) % (p' + 1) = (a^p') % (p' + 1) := by
    rw [← mul_assoc mi.inv (a^p') a,
        Nat.mul_comm mi.inv (a^p'),
        mul_assoc (a^p') mi.inv a,
        Nat.mul_comm mi.inv a,
        mul_mod_right_pure (a^p') (a * mi.inv) (p' + 1),
        mi.inv_eq,
        ← mul_mod_right_pure (a^p') 1 (p' + 1),
        Nat.mul_one]
  -- RHS: (mi.inv * a) % (p'+1) = 1 % (p'+1)  via Nat.mul_comm + inv_eq
  have h_rhs : (mi.inv * a) % (p' + 1) = 1 % (p' + 1) := by
    rw [Nat.mul_comm]
    exact mi.inv_eq
  -- Combine
  rw [← h_lhs, h_mult, h_rhs]

/-! ## Per-prime smokes -/

/-- ModInverse witness: 2 * 3 = 6 ≡ 1 mod 5. -/
def modInv_2_mod_5 : ModInverse 5 2 :=
  { inv := 3, inv_lt := by decide, inv_eq := by decide }

/-- FLT main at p = 5, a = 2: `2^4 = 16 ≡ 1 (mod 5)`. -/
theorem flt_main_5_2 : (2^4) % 5 = 1 % 5 :=
  flt_main 2 4 (by decide)
    E213.Lib.Math.NumberTheory.DyadicFSM.FLT.FreshmanDream.middle_vanish_5 modInv_2_mod_5

/-- ModInverse witness: 3 * 5 = 15 ≡ 1 mod 7. -/
def modInv_3_mod_7 : ModInverse 7 3 :=
  { inv := 5, inv_lt := by decide, inv_eq := by decide }

/-- FLT main at p = 7, a = 3: `3^6 = 729 ≡ 1 (mod 7)`. -/
theorem flt_main_7_3 : (3^6) % 7 = 1 % 7 :=
  flt_main 3 6 (by decide)
    E213.Lib.Math.NumberTheory.DyadicFSM.FLT.FreshmanDream.middle_vanish_7 modInv_3_mod_7

end E213.Lib.Math.NumberTheory.DyadicFSM.FLT.FLTMain
