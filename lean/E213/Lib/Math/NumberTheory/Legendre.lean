import E213.Lib.Math.NumberTheory.PrimeValuation
import E213.Lib.Math.NumberSystems.Real213.ExpLog.CutFactorial
import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum
import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.BinomialTheorem
import E213.Meta.Nat.NatDiv213

/-!
# Legendre — `vₚ(n!)` as a sum, ∅-axiom

Legendre's factorial formula `vₚ(n!) = Σⱼ₌₁ ⌊n/pʲ⌋` splits into two halves:

  1. **Additivity over the factorial product** (this file):
     `vₚ(n!) = Σ_{k<n} vₚ(k+1)` — immediate from `PrimeValuation.vp_mul`
     (`vₚ(a·b) = vₚa + vₚb`) by induction on `n!  = (n)·(n-1)!`, with `vₚ 1 = 0`.
  2. **Double counting** (the remaining half, recorded on the frontier):
     `Σ_{k<n} vₚ(k+1) = Σⱼ ⌊n/pʲ⌋`, by swapping the order of summation
     (`vₚ(k+1) = #{j ≥ 1 : pʲ ∣ k+1}` and `Σ_{k<n} [pʲ ∣ k+1] = ⌊n/pʲ⌋`).

Half 1 already turns the factorial-valuation into a *finite explicit sum*, which is
the form the ζ(3) lcm-bound brick's key-divisibility step consumes per prime power
(against the counting lemma `LcmGrowthChebyshev.count30`).

  * `vp_one` — `vₚ 1 = 0` (`p ≥ 2`).
  * ★★★ `vp_factorial` — `vₚ(n!) = Σ_{k<n} vₚ(k+1)`.

All zero-axiom.
-/

namespace E213.Lib.Math.NumberTheory.Legendre

open E213.Meta.Nat.Valuation (vp vp_lt le_vp_iff mod_zero_of_dvd)
open E213.Meta.Nat.AddMod213 (dvd_of_mod_eq_zero)
open E213.Meta.Nat.PureNat (lt_two_pow)
open E213.Lib.Math.NumberTheory.PrimeValuation (Prime213 vp_mul)
open E213.Lib.Math.NumberSystems.Real213.ExpLog.CutFactorial (factorial factorial_zero
  factorial_succ factorial_pos)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum (sumTo sumTo_succ sumTo_zero)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.BinomialTheorem (sumTo_congr sumTo_add_func)
open E213.Meta.Nat.NatDiv213 (div_sandwich div_eq_of_sandwich mul_witness_iff_mod_eq_zero
  mul_mod_self_pure)

/-- `vₚ 1 = 0` for `p ≥ 2`: the valuation is strictly below its argument. -/
theorem vp_one {p : Nat} (hp : 2 ≤ p) : vp p 1 = 0 :=
  Nat.le_zero.mp (Nat.le_of_lt_succ (vp_lt p 1 hp (by decide)))

/-- ★★★ **`vₚ(n!)` as a finite sum**: `vₚ(n!) = Σ_{k<n} vₚ(k+1)`, by induction on the
    factorial product `(n+1)! = (n+1)·n!` through `PrimeValuation.vp_mul`. -/
theorem vp_factorial {p : Nat} (hp : Prime213 p) :
    ∀ n, vp p (factorial n) = sumTo n (fun k => vp p (k + 1))
  | 0 => by
    show vp p (factorial 0) = 0
    rw [factorial_zero]; exact vp_one hp.1
  | n + 1 => by
    rw [factorial_succ, vp_mul hp (Nat.succ_pos n) (factorial_pos n),
        vp_factorial hp n, sumTo_succ]
    exact Nat.add_comm _ _

/-! ## §2 — Legendre half 2: the double-counting `Σ_{k<n} vₚ(k+1) = Σⱼ ⌊n/p^{j+1}⌋`

The increment route (induction on `n`): the LHS gains `vₚ(n+1)` per step, and the
RHS gains `Σⱼ [p^{j+1} ∣ n+1] = vₚ(n+1)` — `⌊(n+1)/d⌋ = ⌊n/d⌋ + [d∣n+1]` summed
over `j`, with the divisor-count of the valuation `Σ_{j<B}[p^{j+1}∣m] = vₚ m`.  No
Fubini swap. -/

/-- `Σ_{j<B} 1 = B`. -/
private theorem sumTo_const_one : ∀ B, sumTo B (fun _ => (1 : Nat)) = B
  | 0 => rfl
  | B + 1 => by rw [sumTo_succ, sumTo_const_one B]

/-- `Σ_{j<B} 0 = 0`. -/
private theorem sumTo_const_zero : ∀ B, sumTo B (fun _ => (0 : Nat)) = 0
  | 0 => rfl
  | B + 1 => by rw [sumTo_succ, sumTo_const_zero B]

/-- Pure `a·b < a·c → b < c` (`Nat.lt_of_mul_lt_mul_left` carries the full axiom
    set) — by contraposition through `Nat.mul_le_mul_left`. -/
private theorem lt_of_mul_lt_mul_left' {a b c : Nat} (h : a * b < a * c) : b < c := by
  rcases Nat.lt_or_ge b c with hlt | hge
  · exact hlt
  · exact absurd (Nat.mul_le_mul_left a hge) (Nat.not_le.mpr h)

/-- `Σ_{j<B} [j < V] = V` when `V ≤ B`: the indicator is `1` exactly on `[0, V)`. -/
private theorem indLt_sum : ∀ B V, V ≤ B →
    sumTo B (fun j => if j < V then 1 else 0) = V
  | 0, V, hV => by
      have hV0 : V = 0 := Nat.le_antisymm hV (Nat.zero_le V)
      subst hV0; rfl
  | B + 1, V, hV => by
      rcases Nat.lt_or_eq_of_le hV with hlt | heq
      · have hVB : V ≤ B := Nat.le_of_lt_succ hlt
        rw [sumTo_succ]
        show sumTo B (fun j => if j < V then 1 else 0) + (if B < V then 1 else 0) = V
        rw [indLt_sum B V hVB, if_neg (Nat.not_lt.mpr hVB), Nat.add_zero]
      · subst heq
        rw [sumTo_succ]
        show sumTo B (fun j => if j < B + 1 then 1 else 0) + (if B < B + 1 then 1 else 0)
          = B + 1
        rw [sumTo_congr B (fun j => if j < B + 1 then 1 else 0) (fun _ => 1)
              (fun k hk => if_pos (Nat.lt_succ_of_lt hk)), sumTo_const_one B,
            if_pos (Nat.lt_succ_self B)]

/-- The division increment `⌊(n+1)/d⌋ = ⌊n/d⌋ + [d ∣ n+1]` (`d > 0`), divisibility
    read as `(n+1) % d = 0` (pure `decEq`).  Both directions pinned by the
    ÷-sandwich `NatDiv213.div_eq_of_sandwich`. -/
private theorem div_succ_increment (d n : Nat) (hd : 0 < d) :
    (n + 1) / d = n / d + (if (n + 1) % d = 0 then 1 else 0) := by
  have hs := div_sandwich d n hd
  by_cases hmod : (n + 1) % d = 0
  · rw [if_pos hmod]
    obtain ⟨w, hw⟩ := (mul_witness_iff_mod_eq_zero d (n + 1)).mpr hmod
    refine (div_eq_of_sandwich hd ?_ ?_).symm
    · have hlt : d * (n / d) < d * w := by
        rw [hw]; exact Nat.lt_of_le_of_lt hs.1 (Nat.lt_succ_self n)
      rw [← hw]
      exact Nat.mul_le_mul_left d (Nat.succ_le_of_lt (lt_of_mul_lt_mul_left' hlt))
    · exact Nat.lt_of_le_of_lt (Nat.succ_le_of_lt hs.2)
        (by rw [Nat.mul_succ]; exact Nat.lt_add_of_pos_right hd)
  · rw [if_neg hmod, Nat.add_zero]
    refine (div_eq_of_sandwich hd ?_ ?_).symm
    · exact Nat.le_trans hs.1 (Nat.le_succ n)
    · refine Nat.lt_of_le_of_ne (Nat.succ_le_of_lt hs.2) (fun heq => hmod ?_)
      rw [heq]; exact mul_mod_self_pure d (n / d + 1)

/-- The valuation divisor-count: `Σ_{j<B} [p^{j+1} ∣ m] = vₚ m` (`m>0`, `vₚm ≤ B`),
    divisibility read as `m % p^{j+1} = 0`.  The indicator is `[j < vₚ m]`
    (`le_vp_iff`), and `indLt_sum` counts it. -/
private theorem val_count {p : Nat} (hp : Prime213 p) {m : Nat} (hm : 0 < m)
    {B : Nat} (hB : vp p m ≤ B) :
    sumTo B (fun j => if m % p ^ (j + 1) = 0 then 1 else 0) = vp p m := by
  have hq : 2 ≤ p := hp.1
  have hp0 : 0 < p := Nat.lt_of_lt_of_le (by decide) hq
  have hcongr : ∀ k, k < B →
      (if m % p ^ (k + 1) = 0 then 1 else 0) = (if k < vp p m then 1 else 0) := by
    intro j _
    by_cases h : m % p ^ (j + 1) = 0
    · rw [if_pos h, if_pos (show j < vp p m from
        (le_vp_iff p m (j + 1) hq hm).mp (dvd_of_mod_eq_zero h))]
    · rw [if_neg h, if_neg (show ¬ j < vp p m from fun hjv =>
        h (mod_zero_of_dvd (Nat.pos_pow_of_pos (j + 1) hp0)
          ((le_vp_iff p m (j + 1) hq hm).mpr hjv)))]
  rw [sumTo_congr B _ _ hcongr]
  exact indLt_sum B (vp p m) hB

/-- The top term vanishes: `(n+1) / p^{n+1} = 0` (`p ≥ 2`), since `n+1 < 2^{n+1} ≤
    p^{n+1}`. -/
private theorem top_vanish {p : Nat} (hq : 2 ≤ p) (n : Nat) : (n + 1) / p ^ (n + 1) = 0 :=
  Nat.div_eq_of_lt (Nat.lt_of_lt_of_le (lt_two_pow (n + 1)) (Nat.pow_le_pow_left hq (n + 1)))

/-- ★★★ **Legendre's factorial formula**: `vₚ(n!) = Σ_{j<n} ⌊n / p^{j+1}⌋`
    (`p` prime).  Induction on `n`: the LHS gains `vₚ(n+1)` (`vp_mul`), the RHS gains
    `Σ_{j<n} [p^{j+1}∣n+1] = vₚ(n+1)` (`div_succ_increment` summed, then `val_count`),
    with the top term `(n+1)/p^{n+1}` vanishing.  Closes Brick 1's Legendre input. -/
theorem legendre {p : Nat} (hp : Prime213 p) :
    ∀ n, vp p (factorial n) = sumTo n (fun j => n / p ^ (j + 1))
  | 0 => by rw [factorial_zero]; exact vp_one hp.1
  | n + 1 => by
    have hq : 2 ≤ p := hp.1
    have hp0 : 0 < p := Nat.lt_of_lt_of_le (by decide) hq
    have hvle : vp p (n + 1) ≤ n := Nat.le_of_lt_succ (vp_lt p (n + 1) hq (Nat.succ_pos n))
    have hRHS : sumTo (n + 1) (fun j => (n + 1) / p ^ (j + 1))
        = sumTo n (fun j => n / p ^ (j + 1)) + vp p (n + 1) := by
      rw [sumTo_succ]
      show sumTo n (fun j => (n + 1) / p ^ (j + 1)) + (n + 1) / p ^ (n + 1)
        = sumTo n (fun j => n / p ^ (j + 1)) + vp p (n + 1)
      rw [top_vanish hq n, Nat.add_zero,
          sumTo_congr n (fun j => (n + 1) / p ^ (j + 1))
            (fun j => n / p ^ (j + 1) + (if (n + 1) % p ^ (j + 1) = 0 then 1 else 0))
            (fun k _ => div_succ_increment (p ^ (k + 1)) n (Nat.pos_pow_of_pos (k + 1) hp0)),
          ← sumTo_add_func n (fun j => n / p ^ (j + 1))
            (fun j => if (n + 1) % p ^ (j + 1) = 0 then 1 else 0),
          val_count hp (Nat.succ_pos n) hvle]
    rw [factorial_succ, vp_mul hp (Nat.succ_pos n) (factorial_pos n), legendre hp n, hRHS]
    exact Nat.add_comm _ _

end E213.Lib.Math.NumberTheory.Legendre
