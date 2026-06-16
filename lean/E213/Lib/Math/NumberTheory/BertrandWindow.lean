import E213.Lib.Math.NumberTheory.Legendre
import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.ChooseFactorial
import E213.Meta.Nat.NatDiv213

/-!
# Bertrand's middle-window vanishing: primes in `(2n/3, n]` do not divide `C(2n,n)` (∅-axiom)

The one genuinely new ingredient of Erdős's Bertrand proof (the primorial keystone is
already closed).  For a prime `p` with `2n/3 < p ≤ n` and `p² > 2n` (automatic for `n ≥ 5`),
Legendre's formula gives `vₚ(C(2n,n)) = vₚ((2n)!) − 2vₚ(n!) = ⌊2n/p⌋ − 2⌊n/p⌋ = 2 − 2 = 0`
(higher prime powers exceed `2n`), so `p ∤ C(2n,n)`.
-/

namespace E213.Lib.Math.NumberTheory.BertrandWindow

open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Binomial (choose)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.ChooseFactorial (choose_mul_factorials)
open E213.Lib.Math.NumberSystems.Real213.ExpLog.CutFactorial (factorial factorial_pos)
open E213.Lib.Math.NumberTheory.Legendre (legendre)
open E213.Lib.Math.NumberTheory.PrimeValuation (Prime213 vp_mul)
open E213.Meta.Nat.Valuation (vp le_vp_iff)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum (sumTo sumTo_succ sumTo_zero)
open E213.Meta.Nat.NatDiv213 (div_eq_of_sandwich)

/-- A finite sum whose only nonzero term is at index `0`: `Σ_{j<N} f j = f 0`. -/
theorem sumTo_eq_first {f : Nat → Nat} : ∀ {N : Nat}, 1 ≤ N →
    (∀ j, 1 ≤ j → j < N → f j = 0) → sumTo N f = f 0 := by
  intro N
  induction N with
  | zero => intro hN _; exact absurd hN (by decide)
  | succ k ih =>
    intro _ h
    rcases Nat.eq_zero_or_pos k with hk0 | hk
    · subst hk0; rw [sumTo_succ]; show sumTo 0 f + f 0 = f 0; rw [sumTo_zero, Nat.zero_add]
    · rw [sumTo_succ, ih hk (fun j hj1 hjk => h j hj1 (Nat.lt_succ_of_lt hjk)),
          h k hk (Nat.lt_succ_self k), Nat.add_zero]

/-- ★★ **Middle-window vanishing**: a prime `p` with `2n/3 < p ≤ n` and `p² > 2n` does
    **not** divide `C(2n,n)`.  (The new ingredient for Bertrand; the primorial keystone
    `∏_{p≤N} p ≤ 4ᴺ` is already closed.) -/
theorem prime_not_dvd_central_binom_mid {p n : Nat} (hp : Prime213 p)
    (hn : 1 ≤ n) (hpn : p ≤ n) (h3 : 2 * n < 3 * p) (hsq : 2 * n < p * p) :
    ¬ p ∣ choose (2 * n) n := by
  have hp0 : 0 < p := Nat.lt_of_lt_of_le (by decide) hp.1
  have hp1 : 1 ≤ p := Nat.le_trans (by decide) hp.1
  have hpp : p ^ 2 = p * p := by rw [Nat.pow_succ, Nat.pow_one]
  have hn2 : n ≤ 2 * n := Nat.le_mul_of_pos_left n (by decide)
  -- higher prime powers exceed 2n, so those Legendre terms vanish
  have hvanish : ∀ (m : Nat), m ≤ 2 * n → ∀ j, 1 ≤ j → m / p ^ (j + 1) = 0 := by
    intro m hm j hj1
    apply Nat.div_eq_of_lt
    calc m ≤ 2 * n := hm
      _ < p * p := hsq
      _ = p ^ 2 := hpp.symm
      _ ≤ p ^ (j + 1) := Nat.pow_le_pow_right hp1 (Nat.succ_le_succ hj1)
  -- vₚ(n!) = ⌊n/p⌋ = 1
  have hvn : vp p (factorial n) = 1 := by
    rw [legendre hp n, sumTo_eq_first hn (fun j hj1 _ => hvanish n hn2 j hj1)]
    show n / p ^ (0 + 1) = 1
    rw [Nat.pow_one]
    refine (div_eq_of_sandwich hp0 ?_ ?_).symm
    · have : p * 1 = p := by ring_nat
      rw [this]; exact hpn
    · have : p * (1 + 1) = 2 * p := by ring_nat
      rw [this]
      -- n < 2*p  from  2*n < 3*p ≤ 4*p
      have h4 : 2 * n < 4 * p := Nat.lt_of_lt_of_le h3 (by rw [show 4 * p = 3 * p + p from by ring_nat]; exact Nat.le_add_right _ _)
      -- 2*n < 4*p = 2*(2*p) ⟹ n < 2*p
      have h4' : 2 * n < 2 * (2 * p) := by rw [show 2 * (2 * p) = 4 * p from by ring_nat]; exact h4
      rcases Nat.lt_or_ge n (2 * p) with hlt | hge
      · exact hlt
      · exact absurd h4' (Nat.not_lt.mpr (Nat.mul_le_mul_left 2 hge))
  -- vₚ((2n)!) = ⌊2n/p⌋ = 2
  have hv2n : vp p (factorial (2 * n)) = 2 := by
    rw [legendre hp (2 * n), sumTo_eq_first (Nat.le_trans hn hn2) (fun j hj1 _ => hvanish (2 * n) (Nat.le_refl _) j hj1)]
    show 2 * n / p ^ (0 + 1) = 2
    rw [Nat.pow_one]
    refine (div_eq_of_sandwich hp0 ?_ ?_).symm
    · have : p * 2 = 2 * p := by ring_nat
      rw [this]
      -- 2*p ≤ 2*n  from  p ≤ n
      exact Nat.mul_le_mul_left 2 hpn
    · have : p * (2 + 1) = 3 * p := by ring_nat
      rw [this]; exact h3
  -- C(2n,n)·(n!·n!) = (2n)!  ⟹  vₚ((2n)!) = vₚ(C) + 2vₚ(n!)  ⟹  vₚ(C) = 2 − 2 = 0
  have hfn : 0 < factorial n := factorial_pos n
  have hid : choose (2 * n) n * (factorial n * factorial n) = factorial (2 * n) := by
    rw [show 2 * n = n + n from by ring_nat]; exact choose_mul_factorials n n
  have hcpos : 0 < choose (2 * n) n := by
    rcases Nat.eq_zero_or_pos (choose (2 * n) n) with h0 | h
    · exfalso; rw [h0, Nat.zero_mul] at hid
      exact absurd hid.symm (Nat.ne_of_gt (factorial_pos (2 * n)))
    · exact h
  have hvp := congrArg (vp p) hid
  rw [vp_mul hp hcpos (Nat.mul_pos hfn hfn), vp_mul hp hfn hfn, hvn, hv2n] at hvp
  -- hvp : vp p C + (1 + 1) = 2
  have hvC : vp p (choose (2 * n) n) = 0 := by
    have h2 : vp p (choose (2 * n) n) + 2 = 2 := hvp
    rcases Nat.eq_zero_or_pos (vp p (choose (2 * n) n)) with h0 | hpos
    · exact h0
    · exfalso
      have hgt : 2 < vp p (choose (2 * n) n) + 2 := Nat.lt_add_of_pos_left hpos
      rw [h2] at hgt; exact absurd hgt (Nat.lt_irrefl 2)
  -- p ∤ C since vp = 0
  intro hdvd
  have : 1 ≤ vp p (choose (2 * n) n) :=
    (le_vp_iff p (choose (2 * n) n) 1 hp.1 hcpos).mp (by rw [Nat.pow_one]; exact hdvd)
  rw [hvC] at this
  exact absurd this (by decide)

end E213.Lib.Math.NumberTheory.BertrandWindow
