import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGcd
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinDvd
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCompletion
import E213.Lib.Math.NumberTheory.ModArith.PrimeSquareFactor
import E213.Meta.Int213.OrderMul

/-!
# EisensteinSplit — Euclid's lemma in `ℤ[ω]` and the split-prime norm (Phase 2c-euclid)

Given `p` prime with `p ∣ x² + x + 1`, the element `x − ω = ⟨x, −1⟩` satisfies
`(x−ω)·conj(x−ω) = ofInt(x²+x+1)` (`mul_conj_self` + `normSq_x_sub_omega`), so
`ofInt p ∣ (x−ω)·conj(x−ω)` while `ofInt p ∤ (x−ω)` and `ofInt p ∤ conj(x−ω)` (both have a
unit imaginary part).  The Euclidean gcd `d = gcd(ofInt p, x−ω)` is then a **proper non-unit
divisor**: `ofInt p = d·e` with `d, e` non-units, so `p² = ‖d‖²·‖e‖²` with both `≥ 2`, hence
`‖d‖² = p` — i.e. `p = a² − ab + b²`.

This file builds the setup; the reducibility/norm conclusion follows.

  * `ofInt_mul` — `ofInt (a·b) = ofInt a · ofInt b`.
  * `cyclotomic_factor` — `⟨x,−1⟩ · conj⟨x,−1⟩ = ofInt (x² + x + 1)`.
  * `not_dvd_unit_im` — a non-unit `p` divides no `θ` with `θ.im = ±1`.

All zero-axiom.
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinSplit

open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega (ZOmega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega.ZOmega
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinDivStep
  (mul_conj_self normSq_conj)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinDvd
  (normSq_dvd_of_dvd unit_of_normSq_one normSq_one_of_unit dvd_components_of_dvd
   normSq_x_sub_omega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinDivStep (normSq_pos)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCompletion (ofInt_normSq)
open E213.Lib.Math.NumberTheory.ModArith.PrimeSquareFactor (eq_p_of_mul_eq_psq)
open E213.Meta.Int213.OrderMul (natAbs_cast_of_nonneg)

/-! ## §1 — `ofInt` is multiplicative -/

/-- `ofInt (a·b) = ofInt a · ofInt b`. -/
theorem ofInt_mul (a b : Int) : ZOmega.ofInt (a * b) = ZOmega.ofInt a * ZOmega.ofInt b := by
  refine ZOmega.ext ?_ ?_
  · show a * b = a * b - 0 * 0
    rw [E213.Meta.Int213.zero_mul, E213.Meta.Int213.Order.sub_zero]
  · show (0 : Int) = a * 0 + 0 * b - 0 * 0
    rw [E213.Meta.Int213.mul_comm a 0, E213.Meta.Int213.zero_mul, E213.Meta.Int213.zero_mul,
        E213.Meta.Int213.zero_mul, E213.Meta.Int213.zero_add, E213.Meta.Int213.Order.sub_zero]

/-! ## §2 — the cyclotomic factorization -/

/-- `⟨x,−1⟩ · conj⟨x,−1⟩ = ofInt (x² + x + 1)` (the norm realised as a ring element). -/
theorem cyclotomic_factor (x : Int) :
    (⟨x, -1⟩ : ZOmega) * (⟨x, -1⟩ : ZOmega).conj = ZOmega.ofInt (x * x + x + 1) := by
  rw [mul_conj_self, normSq_x_sub_omega]

/-! ## §3 — a non-unit does not divide an element with unit imaginary part -/

/-- If `p ∣ θ` (as `ofInt p · c`) and `θ.im = 1` or `−1`, then `p ∣ 1` — excluded for a
    prime.  (Takes `¬ p ∣ 1`, true for any prime, as hypothesis.) -/
theorem not_dvd_unit_im (p : Int) (θ : ZOmega) (hp : ¬ (p ∣ (1 : Int)))
    (him : θ.im = 1 ∨ θ.im = -1) : ¬ ∃ c : ZOmega, θ = ZOmega.ofInt p * c := by
  intro hd
  obtain ⟨c, hc⟩ := hd
  have hpim : p ∣ θ.im := (dvd_components_of_dvd p θ c hc).2
  rcases him with h1 | h1
  · rw [h1] at hpim; exact hp hpim
  · rw [h1] at hpim
    obtain ⟨k, hk⟩ := hpim
    exact hp ⟨-k, by rw [E213.Meta.Int213.mul_neg, ← hk, Int.neg_neg]⟩

/-! ## §4 — a non-unit factorization of `ofInt p` has a norm-`p` factor -/

/-- ★★★ **The norm-arithmetic core.**  If `ofInt p = d·e` with `d, e` non-units (`‖·‖² ≠ 1`)
    and `p` prime, then `‖d‖² = p` — because `‖d‖²·‖e‖² = p²` with both factors `≥ 2`. -/
theorem norm_factor_eq_p (p : Nat) (hp2 : 2 ≤ p) (hpr : ∀ m, m ∣ p → m = 1 ∨ m = p)
    (d e : ZOmega) (he : ZOmega.ofInt (p : Int) = d * e)
    (hd1 : d.normSq ≠ 1) (he1 : e.normSq ≠ 1) : d.normSq = (p : Int) := by
  have hPne : ZOmega.ofInt (p : Int) ≠ 0 := by
    intro h
    have hpr0 : (p : Int) = 0 := congrArg ZOmega.re h
    have : p = 0 := Int.ofNat.inj hpr0
    rw [this] at hp2; exact absurd hp2 (by decide)
  have hdne : d ≠ 0 := fun h => hPne (by rw [he, h]; exact E213.Meta.Algebra213.Ring213.zero_mul e)
  have hene : e ≠ 0 := fun h => hPne (by rw [he, h]; exact E213.Meta.Algebra213.Ring213.mul_zero d)
  have hdpos : 0 < d.normSq := normSq_pos d hdne
  have hepos : 0 < e.normSq := normSq_pos e hene
  have hndc : ((d.normSq.natAbs : Int)) = d.normSq :=
    natAbs_cast_of_nonneg (E213.Meta.Int213.Order.le_of_lt hdpos)
  have hnec : ((e.normSq.natAbs : Int)) = e.normSq :=
    natAbs_cast_of_nonneg (E213.Meta.Int213.Order.le_of_lt hepos)
  -- ‖d‖²·‖e‖² = p·p
  have hprod : d.normSq * e.normSq = (p : Int) * (p : Int) := by
    rw [← ZOmega.normSq_mul, ← he, ofInt_normSq]
  -- Nat version: nd·ne = p·p
  have hprodN : d.normSq.natAbs * e.normSq.natAbs = p * p := by
    have hcast : ((d.normSq.natAbs * e.normSq.natAbs : Nat) : Int) = ((p * p : Nat) : Int) := by
      rw [Int.ofNat_mul, hndc, hnec, hprod, Int.ofNat_mul]
    exact Int.ofNat.inj hcast
  -- nd ≥ 2, ne ≥ 2
  have hkey : ∀ m : Nat, m ≠ 0 → m ≠ 1 → 2 ≤ m := by
    intro m hm0 hm1
    rcases m with _ | _ | k
    · exact absurd rfl hm0
    · exact absurd rfl hm1
    · exact Nat.le_add_left 2 k
  have hge2 : ∀ (q : ZOmega), 0 < q.normSq → q.normSq ≠ 1 → 2 ≤ q.normSq.natAbs := by
    intro q hqpos hq1
    have hqc : ((q.normSq.natAbs : Int)) = q.normSq :=
      natAbs_cast_of_nonneg (E213.Meta.Int213.Order.le_of_lt hqpos)
    have hne0 : q.normSq.natAbs ≠ 0 := by
      intro h0; rw [h0] at hqc; rw [← hqc] at hqpos; exact absurd hqpos (by decide)
    have hne1 : q.normSq.natAbs ≠ 1 := by
      intro h1; rw [h1] at hqc; exact hq1 hqc.symm
    exact hkey _ hne0 hne1
  have hndge : 2 ≤ d.normSq.natAbs := hge2 d hdpos hd1
  have hnege : 2 ≤ e.normSq.natAbs := hge2 e hepos he1
  -- eq_p
  have hpow : d.normSq.natAbs * e.normSq.natAbs = p ^ 2 := by
    rw [hprodN, Nat.pow_succ, Nat.pow_one]
  have hnd : d.normSq.natAbs = p :=
    eq_p_of_mul_eq_psq p d.normSq.natAbs e.normSq.natAbs hp2 hpr hndge hnege hpow
  rw [← hndc, hnd]

end E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinSplit
