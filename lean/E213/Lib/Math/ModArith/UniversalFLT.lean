import E213.Lib.Math.ModArith.ModBezoutInvariant
import E213.Lib.Math.DyadicFSM.FLT.FreshmanDream
import E213.Lib.Math.DyadicFSM.FLT.FLTPrimary
import E213.Lib.Math.DyadicFSM.FLT.FLTMain
/-!
# Universal FLT (Bezout-based)

Combines `modInverseFromBezout` (Part 30, Bezout marathon) with the
conditional FLT framework (Parts 14-22) to get universal forms:

  · **`universal_middle_binomial_vanish`** : for `1 < p` and the
    `h_prime_gcd` hypothesis (encoding primality as `gcd(m, p) = 1`
    for all `0 < m < p`), all middle binomial coefficients vanish
    mod p.
  · **`universal_freshman_dream`** : direct corollary.
  · **`universal_flt_primary`** : `a^p ≡ a (mod p)`.
  · **`universal_flt_main`** : `a^(p-1) ≡ 1 (mod p)` for `a` coprime
    to `p`.

The `h_prime_gcd` hypothesis is decidable per specific prime
(finite quantifier).  Universal abstract "p is Prime" would
require a `Prime` predicate (out of scope this session); the
gcd-based encoding is operationally equivalent.

All declarations PURE.
-/

namespace E213.Lib.Math.ModArith.UniversalFLT

open E213.Lib.Math.ModArith.ModBezout (modBezout)
open E213.Lib.Math.ModArith.ModBezoutInvariant (modInverseFromBezout)
open E213.Lib.Math.DyadicFSM.FLT.Binomial (choose)
open E213.Lib.Math.DyadicFSM.FLT.ChoosePrime (choose_p_dvd_of_inverse)
open E213.Lib.Math.DyadicFSM.FLT.FreshmanDream (freshman_dream)
open E213.Lib.Math.DyadicFSM.FLT.FLTPrimary (flt_primary)
open E213.Lib.Math.DyadicFSM.FLT.FLTMain (flt_main)
open E213.Lib.Math.DyadicFSM.MulOrderPigeonhole (ModInverse)

/-- ★ **Universal middle-binomial vanishing**:
    For `1 < p` and `h_prime_gcd` (every `0 < m < p` is coprime
    to `p`), all middle binomial coefficients vanish mod p:

      `∀ k, k < p - 1 → (choose p (k + 1)) % p = 0`.

    PURE.  Per-`k`, construct `ModInverse p (k+1)` via Bezout
    (using `modInverseFromBezout`), then apply
    `choose_p_dvd_of_inverse` (Part 15). -/
theorem universal_middle_binomial_vanish
    (p : Nat) (hp : 1 < p)
    (h_prime_gcd : ∀ m, 0 < m → m < p → (modBezout m p).1 = 1) :
    ∀ k, k < p - 1 → (choose p (k + 1)) % p = 0 := by
  intro k hk
  have hp_pos : 0 < p := Nat.lt_of_succ_lt hp
  have h_k1_pos : 0 < k + 1 := Nat.succ_pos k
  -- k < p - 1 means k + 1 ≤ p - 1, i.e., k + 1 < p
  have h_k1_lt : k + 1 < p := by
    -- hk : k < p - 1. So k + 1 ≤ p - 1 < p.
    have h1 : k + 1 ≤ p - 1 := hk
    have h2 : p - 1 < p := Nat.sub_lt hp_pos Nat.one_pos
    exact Nat.lt_of_le_of_lt h1 h2
  -- Build the ModInverse via Bezout
  let mi : ModInverse p (k + 1) :=
    modInverseFromBezout (k + 1) p hp_pos
      (h_prime_gcd (k + 1) h_k1_pos h_k1_lt)
  exact choose_p_dvd_of_inverse p k hp mi

/-- ★★ **Universal freshman's dream**:
    `(a + 1)^p ≡ a^p + 1 (mod p)` for `1 < p` and `h_prime_gcd`.

    PURE.  Direct corollary of `universal_middle_binomial_vanish`
    + the conditional `freshman_dream` (Part 20). -/
theorem universal_freshman_dream
    (a p : Nat) (hp : 1 < p)
    (h_prime_gcd : ∀ m, 0 < m → m < p → (modBezout m p).1 = 1) :
    ((a + 1)^p) % p = (a^p + 1) % p := by
  -- Parameterise as p = p' + 1 with hp' : 1 ≤ p' (so p ≥ 2 matches hp : 1 < p)
  cases p with
  | zero => exact absurd hp (Nat.not_lt_zero 1)
  | succ p' =>
    have hp_pp1 : 1 < p' + 1 := hp
    have hp' : 1 ≤ p' := Nat.le_of_succ_le_succ hp_pp1
    -- universal middle-binomial vanish gives the h_middle hypothesis
    have h_middle : ∀ k, k < p' →
        (choose (p' + 1) (k + 1)) % (p' + 1) = 0 := by
      intro k hk
      -- k < p' means k < (p' + 1) - 1
      have hk' : k < (p' + 1) - 1 := by
        show k < p' + 1 - 1
        rw [E213.Tactic.NatHelper.add_sub_cancel_right p' 1]
        exact hk
      exact universal_middle_binomial_vanish (p' + 1) hp_pp1 h_prime_gcd k hk'
    exact freshman_dream a p' hp' h_middle

/-- ★★★ **Universal FLT primary** form:
    `a^p ≡ a (mod p)` for `1 < p` and `h_prime_gcd`.

    PURE.  Direct corollary of `universal_freshman_dream` + the
    conditional `flt_primary` (Part 21). -/
theorem universal_flt_primary
    (a p : Nat) (hp : 1 < p)
    (h_prime_gcd : ∀ m, 0 < m → m < p → (modBezout m p).1 = 1) :
    (a^p) % p = a % p := by
  cases p with
  | zero => exact absurd hp (Nat.not_lt_zero 1)
  | succ p' =>
    have hp_pp1 : 1 < p' + 1 := hp
    have hp' : 1 ≤ p' := Nat.le_of_succ_le_succ hp_pp1
    have h_middle : ∀ k, k < p' →
        (choose (p' + 1) (k + 1)) % (p' + 1) = 0 := by
      intro k hk
      have hk' : k < (p' + 1) - 1 := by
        show k < p' + 1 - 1
        rw [E213.Tactic.NatHelper.add_sub_cancel_right p' 1]
        exact hk
      exact universal_middle_binomial_vanish (p' + 1) hp_pp1 h_prime_gcd k hk'
    exact flt_primary p' hp' h_middle a

/-- ★★★★ **Universal FLT main** form:
    `a^(p-1) ≡ 1 (mod p)` for `1 < p`, `0 < a`, `a < p`,
    and `h_prime_gcd`.

    PURE.  Builds `ModInverse p a` via Bezout, then applies
    `flt_main` (Part 22) with universally-derived `h_middle`. -/
theorem universal_flt_main
    (a p : Nat) (hp : 1 < p)
    (ha_pos : 0 < a) (ha_lt : a < p)
    (h_prime_gcd : ∀ m, 0 < m → m < p → (modBezout m p).1 = 1) :
    (a^(p - 1)) % p = 1 % p := by
  cases p with
  | zero => exact absurd hp (Nat.not_lt_zero 1)
  | succ p' =>
    have hp_pp1 : 1 < p' + 1 := hp
    have hp' : 1 ≤ p' := Nat.le_of_succ_le_succ hp_pp1
    have hp_pos : 0 < p' + 1 := Nat.succ_pos _
    -- h_a_gcd : (modBezout a (p'+1)).1 = 1
    have h_a_gcd : (modBezout a (p' + 1)).1 = 1 :=
      h_prime_gcd a ha_pos ha_lt
    -- Build ModInverse for a
    let mi : ModInverse (p' + 1) a :=
      modInverseFromBezout a (p' + 1) hp_pos h_a_gcd
    -- Universal middle-binomial vanish
    have h_middle : ∀ k, k < p' →
        (choose (p' + 1) (k + 1)) % (p' + 1) = 0 := by
      intro k hk
      have hk' : k < (p' + 1) - 1 := by
        show k < p' + 1 - 1
        rw [E213.Tactic.NatHelper.add_sub_cancel_right p' 1]
        exact hk
      exact universal_middle_binomial_vanish (p' + 1) hp_pp1 h_prime_gcd k hk'
    -- Apply flt_main
    show (a^p') % (p' + 1) = 1 % (p' + 1)
    exact flt_main a p' hp' h_middle mi

/-! ## Per-prime smokes -/

/-- Smoke: at p=5, the prime-gcd hypothesis verified by enumeration.
    Case on m without destructuring hypotheses (which pull Quot.sound). -/
theorem prime_gcd_5 : ∀ m, 0 < m → m < 5 → (modBezout m 5).1 = 1 := by
  intro m hm hmlt
  match m with
  | 0 => exact absurd hm (Nat.lt_irrefl 0)
  | 1 => decide
  | 2 => decide
  | 3 => decide
  | 4 => decide
  | n + 5 => exact absurd hmlt (Nat.not_lt_of_le (Nat.le_add_left 5 n))

/-- Smoke: universal FLT main at p=5, a=2: 2^4 ≡ 1 mod 5. -/
theorem universal_flt_main_5_2 : (2^4) % 5 = 1 % 5 :=
  universal_flt_main 2 5 (by decide) (by decide) (by decide) prime_gcd_5

/-- Smoke: at p=7, prime-gcd via enumeration. -/
theorem prime_gcd_7 : ∀ m, 0 < m → m < 7 → (modBezout m 7).1 = 1 := by
  intro m hm hmlt
  match m with
  | 0 => exact absurd hm (Nat.lt_irrefl 0)
  | 1 => decide
  | 2 => decide
  | 3 => decide
  | 4 => decide
  | 5 => decide
  | 6 => decide
  | n + 7 => exact absurd hmlt (Nat.not_lt_of_le (Nat.le_add_left 7 n))

theorem universal_flt_main_7_3 : (3^6) % 7 = 1 % 7 :=
  universal_flt_main 3 7 (by decide) (by decide) (by decide) prime_gcd_7

/-- Smoke: at p=11, prime-gcd via enumeration. -/
theorem prime_gcd_11 : ∀ m, 0 < m → m < 11 → (modBezout m 11).1 = 1 := by
  intro m hm hmlt
  match m with
  | 0 => exact absurd hm (Nat.lt_irrefl 0)
  | 1 => decide
  | 2 => decide
  | 3 => decide
  | 4 => decide
  | 5 => decide
  | 6 => decide
  | 7 => decide
  | 8 => decide
  | 9 => decide
  | 10 => decide
  | n + 11 => exact absurd hmlt (Nat.not_lt_of_le (Nat.le_add_left 11 n))

/-- Smoke: universal FLT main at p=11, a=4 (= sqrt5 mod 11): 4^10 ≡ 1 mod 11. -/
theorem universal_flt_main_11_4 : (4^10) % 11 = 1 % 11 :=
  universal_flt_main 4 11 (by decide) (by decide) (by decide) prime_gcd_11

end E213.Lib.Math.ModArith.UniversalFLT
