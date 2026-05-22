import E213.Lib.Math.DyadicFSM.FLT.BinomialTheorem
import E213.Lib.Math.DyadicFSM.FLT.ChoosePrime
/-!
# Freshman's dream — `(a + 1)^p ≡ a^p + 1 (mod p)` for prime p

The classical FLT freshman's dream, conditional on the middle
binomial coefficients vanishing mod p:

  `∀ k, 0 < k < p → (choose p k) % p = 0`

This hypothesis holds for primes p (via Euclid's lemma applied to
`choose_succ_mul` + coprimality of `k` with `p`), captured by
`choose_p_dvd_of_inverse` (Part 15) per explicit-inverse witness.

Given the hypothesis (provable per-prime via `decide` for each
specific prime), the freshman's dream is a direct corollary of the
binomial theorem (Part 19) + middle-term vanishing
(`sumTo_eq_zero_of_all_zero`, Part 16).

All declarations PURE.
-/

namespace E213.Lib.Math.DyadicFSM.FLT.FreshmanDream

open E213.Lib.Math.DyadicFSM.FLT.Binomial
  (choose choose_zero_right choose_self)
open E213.Lib.Math.DyadicFSM.FLT.Sum
  (sumTo sumTo_succ sumTo_eq_zero_of_all_zero)
open E213.Lib.Math.DyadicFSM.FLT.BinomialTheorem
  (binomSum binom_theorem_b_eq_one sumTo_split_first)
open E213.Meta.Nat.MulMod213 (mul_mod_left_pure)
open E213.Meta.Nat.AddMod213 (add_mod_gen mod_mod)

/-- Helper: `X % p = 0 → (X · Y) % p = 0`. -/
theorem mul_mod_zero_left (X Y p : Nat) (h : X % p = 0) :
    (X * Y) % p = 0 := by
  rw [mul_mod_left_pure X Y p, h, Nat.zero_mul]
  rfl

/-- ★★★★★ **Freshman's dream** (conditional on middle-binomial
    vanishing mod p):

    `((a + 1)^p) % p = (a^p + 1) % p`

    given `1 < p` and `∀ k, k < p - 1 → (choose p (k + 1)) % p = 0`
    (the hypothesis that all middle binomial coefficients vanish
    mod p — holds for primes via `choose_p_dvd_of_inverse`).

    Parameterised as `p = p' + 1` with `1 ≤ p'` (so `p ≥ 2`).

    PURE.  Direct corollary of `binom_theorem_b_eq_one` (Part 19) +
    `sumTo_eq_zero_of_all_zero` (Part 16) + Nat mod manipulations. -/
theorem freshman_dream (a p' : Nat) (_hp' : 1 ≤ p')
    (h_middle : ∀ k, k < p' →
      (choose (p' + 1) (k + 1)) % (p' + 1) = 0) :
    ((a + 1)^(p' + 1)) % (p' + 1) = (a^(p' + 1) + 1) % (p' + 1) := by
  -- Step 1: apply binomial theorem at b=1
  rw [binom_theorem_b_eq_one a (p' + 1)]
  -- Goal: binomSum a (p' + 1) % (p' + 1) = (a^(p' + 1) + 1) % (p' + 1)
  -- binomSum unfolds to sumTo (p' + 2) (fun k => choose (p'+1) k * a^k)
  show (sumTo (p' + 2) (fun k => choose (p' + 1) k * a^k)) % (p' + 1)
     = (a^(p' + 1) + 1) % (p' + 1)
  -- Step 2: split first term + extract last
  rw [sumTo_split_first (p' + 1) (fun k => choose (p' + 1) k * a^k)]
  -- Goal: ((fun k => C (p'+1) k * a^k) 0 + sumTo (p' + 1) (fun k => (...) (k+1))) % (p' + 1) = ...
  show (choose (p' + 1) 0 * a^0
        + sumTo (p' + 1) (fun k => choose (p' + 1) (k + 1) * a^(k + 1)))
       % (p' + 1) = (a^(p' + 1) + 1) % (p' + 1)
  rw [choose_zero_right, Nat.one_mul]
  show (1 + sumTo (p' + 1) (fun k => choose (p' + 1) (k + 1) * a^(k + 1)))
       % (p' + 1) = (a^(p' + 1) + 1) % (p' + 1)
  -- Step 3: extract last term from inner sumTo (p' + 1)
  show (1 + (sumTo p' (fun k => choose (p' + 1) (k + 1) * a^(k + 1))
              + choose (p' + 1) (p' + 1) * a^(p' + 1)))
       % (p' + 1) = (a^(p' + 1) + 1) % (p' + 1)
  rw [choose_self, Nat.one_mul]
  -- Goal: (1 + (sumTo p' (...) + a^(p'+1))) % (p'+1) = (a^(p'+1) + 1) % (p'+1)
  -- Step 4: rearrange Nat additions to bring sumTo p' next to others
  rw [show 1 + (sumTo p' (fun k => choose (p' + 1) (k + 1) * a^(k + 1))
                + a^(p' + 1))
        = sumTo p' (fun k => choose (p' + 1) (k + 1) * a^(k + 1))
          + (1 + a^(p' + 1)) from by
        rw [Nat.add_comm 1 (sumTo p' _ + a^(p' + 1)),
            Nat.add_assoc (sumTo p' _) (a^(p' + 1)) 1,
            Nat.add_comm (a^(p' + 1)) 1]]
  -- Goal: (sumTo p' (...) + (1 + a^(p'+1))) % (p'+1) = (a^(p'+1) + 1) % (p'+1)
  -- Step 5: split outer mod, apply middle vanishing, recombine
  rw [add_mod_gen (sumTo p' (fun k => choose (p' + 1) (k + 1) * a^(k + 1)))
        (1 + a^(p' + 1)) (p' + 1)]
  -- Apply middle vanishing on sumTo p' part
  have h_zero : (sumTo p' (fun k => choose (p' + 1) (k + 1) * a^(k + 1)))
              % (p' + 1) = 0 := by
    apply sumTo_eq_zero_of_all_zero (p' + 1) p'
      (fun k => choose (p' + 1) (k + 1) * a^(k + 1))
    intro k hk
    exact mul_mod_zero_left (choose (p' + 1) (k + 1)) (a^(k + 1)) (p' + 1)
      (h_middle k hk)
  rw [h_zero, Nat.zero_add, mod_mod]
  -- Goal: (1 + a^(p'+1)) % (p'+1) = (a^(p'+1) + 1) % (p'+1)
  rw [Nat.add_comm 1 (a^(p' + 1))]

/-! ## Per-prime smokes -/

/-- All middle binomial coefficients vanish mod 5: decidable. -/
theorem middle_vanish_5 :
    ∀ k, k < 4 → (choose 5 (k + 1)) % 5 = 0 := by decide

/-- Freshman's dream at p = 5: `(a + 1)^5 ≡ a^5 + 1 (mod 5)`. -/
theorem freshman_dream_5 (a : Nat) :
    ((a + 1)^5) % 5 = (a^5 + 1) % 5 :=
  freshman_dream a 4 (by decide) middle_vanish_5

/-- All middle binomial coefficients vanish mod 7: decidable. -/
theorem middle_vanish_7 :
    ∀ k, k < 6 → (choose 7 (k + 1)) % 7 = 0 := by decide

/-- Freshman's dream at p = 7: `(a + 1)^7 ≡ a^7 + 1 (mod 7)`. -/
theorem freshman_dream_7 (a : Nat) :
    ((a + 1)^7) % 7 = (a^7 + 1) % 7 :=
  freshman_dream a 6 (by decide) middle_vanish_7

end E213.Lib.Math.DyadicFSM.FLT.FreshmanDream
