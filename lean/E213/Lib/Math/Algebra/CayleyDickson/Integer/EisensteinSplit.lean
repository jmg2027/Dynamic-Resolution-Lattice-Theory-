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
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGcd
  (gcd_bezout ofInt_one_mul mul_ofInt_one)
open E213.Meta.Algebra213 (CommRing213)
open E213.Meta.Algebra213.Ring213 (add_mul mul_add mul_assoc)
open E213.Meta.Algebra213.CommRing213 renaming mul_comm → zmul_comm

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

/-! ## §3b — the unit-Bezout ⟹ `p ∣ conj(x−ω)` engine -/

/-- `a·b·c = a·c·b` over any `CommRing213`. -/
theorem mul_right_comm213 {α} [CommRing213 α] (a b c : α) : a * b * c = a * c * b := by
  rw [mul_assoc, zmul_comm b c, ← mul_assoc]

/-- From a **unit Bezout** `ofInt 1 = s·ofInt p + t·(x−ω)` (and `x²+x+1 = p·k`), the prime
    `ofInt p` divides `conj(x−ω)` (multiply through by `conj(x−ω)`, factor out `ofInt p` using
    the cyclotomic factorization `(x−ω)·conj(x−ω) = ofInt(x²+x+1) = ofInt p · ofInt k`). -/
theorem unit_bezout_dvd_conj (p k x : Int) (s t : ZOmega)
    (hu : ZOmega.ofInt 1 = s * ZOmega.ofInt p + t * (⟨x, -1⟩ : ZOmega))
    (hk : x * x + x + 1 = p * k) :
    ∃ c : ZOmega, (⟨x, -1⟩ : ZOmega).conj = ZOmega.ofInt p * c := by
  refine ⟨s * (⟨x, -1⟩ : ZOmega).conj + t * ZOmega.ofInt k, ?_⟩
  have e1 : (s * ZOmega.ofInt p) * (⟨x, -1⟩ : ZOmega).conj
          = ZOmega.ofInt p * (s * (⟨x, -1⟩ : ZOmega).conj) := by
    rw [zmul_comm s (ZOmega.ofInt p), mul_assoc]
  have e2 : t * (ZOmega.ofInt p * ZOmega.ofInt k)
          = ZOmega.ofInt p * (t * ZOmega.ofInt k) := by
    rw [← mul_assoc, zmul_comm t (ZOmega.ofInt p), mul_assoc]
  calc (⟨x, -1⟩ : ZOmega).conj
      = ZOmega.ofInt 1 * (⟨x, -1⟩ : ZOmega).conj := (ofInt_one_mul _).symm
    _ = (s * ZOmega.ofInt p + t * ⟨x, -1⟩) * (⟨x, -1⟩ : ZOmega).conj := by rw [hu]
    _ = (s * ZOmega.ofInt p) * (⟨x, -1⟩ : ZOmega).conj
          + (t * ⟨x, -1⟩) * (⟨x, -1⟩ : ZOmega).conj := by rw [add_mul]
    _ = (s * ZOmega.ofInt p) * (⟨x, -1⟩ : ZOmega).conj
          + t * ((⟨x, -1⟩ : ZOmega) * (⟨x, -1⟩ : ZOmega).conj) := by
        rw [mul_assoc t (⟨x, -1⟩ : ZOmega) (⟨x, -1⟩ : ZOmega).conj]
    _ = (s * ZOmega.ofInt p) * (⟨x, -1⟩ : ZOmega).conj
          + t * (ZOmega.ofInt p * ZOmega.ofInt k) := by rw [cyclotomic_factor, hk, ofInt_mul]
    _ = ZOmega.ofInt p * (s * (⟨x, -1⟩ : ZOmega).conj)
          + ZOmega.ofInt p * (t * ZOmega.ofInt k) := by rw [e1, e2]
    _ = ZOmega.ofInt p * (s * (⟨x, -1⟩ : ZOmega).conj + t * ZOmega.ofInt k) := by rw [← mul_add]

/-- The Euclidean gcd `d = s·ofInt p + t·(x−ω)` being a **unit** (`‖d‖²=1`) forces
    `ofInt p ∣ conj(x−ω)` — scale the Bezout by `conj d` to `ofInt 1 = (s·conj d)·ofInt p +
    (t·conj d)·(x−ω)`, then `unit_bezout_dvd_conj`. -/
theorem dvd_conj_of_gcd_unit (p k x : Int) (d s t : ZOmega)
    (hbez : d = s * ZOmega.ofInt p + t * (⟨x, -1⟩ : ZOmega)) (hdunit : d.normSq = 1)
    (hk : x * x + x + 1 = p * k) :
    ∃ c : ZOmega, (⟨x, -1⟩ : ZOmega).conj = ZOmega.ofInt p * c := by
  have hdc : d * d.conj = ZOmega.ofInt 1 := unit_of_normSq_one d hdunit
  have hsb : (s * ZOmega.ofInt p + t * (⟨x, -1⟩ : ZOmega)) * d.conj = ZOmega.ofInt 1 := by
    rw [← hbez]; exact hdc
  have hbez1 : ZOmega.ofInt 1
      = (s * d.conj) * ZOmega.ofInt p + (t * d.conj) * (⟨x, -1⟩ : ZOmega) := by
    rw [← hsb, add_mul, mul_right_comm213 s (ZOmega.ofInt p) d.conj,
        mul_right_comm213 t (⟨x, -1⟩ : ZOmega) d.conj]
  exact unit_bezout_dvd_conj p k x (s * d.conj) (t * d.conj) hbez1 hk

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

/-! ## §5 — the split: `p ∣ x²+x+1` ⟹ `p` is a norm in `ℤ[ω]` -/

/-- ★★★★ **The Eisenstein split.**  If `p` is prime and `p ∣ x² + x + 1` (a primitive cube
    root mod `p`), then `p = ‖d‖²` for some `d ∈ ℤ[ω]` — i.e. `p = a² − ab + b²`.  The
    Euclidean gcd `d = gcd(ofInt p, x−ω)` is a proper non-unit divisor: it is non-unit (else
    a unit Bezout would give `p ∣ conj(x−ω)`, impossible), and its cofactor `e` is non-unit
    (else `p ∣ (x−ω)`, impossible); so `ofInt p = d·e` reducible and `norm_factor_eq_p` gives
    `‖d‖² = p`.  (`¬ (p:ℤ) ∣ 1` — true for any prime — is taken as a hypothesis.) -/
theorem split_norm (p : Nat) (hp2 : 2 ≤ p) (hpr : ∀ m, m ∣ p → m = 1 ∨ m = p)
    (hp1 : ¬ ((p : Int) ∣ (1 : Int)))
    (x : Int) (hx : (p : Int) ∣ (x * x + x + 1)) :
    ∃ d : ZOmega, d.normSq = (p : Int) := by
  obtain ⟨k, hk⟩ := hx
  obtain ⟨d, s, t, hbez, hdP, hdω⟩ :=
    gcd_bezout (⟨x, -1⟩ : ZOmega).normSq.natAbs (ZOmega.ofInt (p : Int)) (⟨x, -1⟩ : ZOmega)
      (Nat.le_refl _)
  obtain ⟨e, he⟩ := hdP
  refine ⟨d, ?_⟩
  apply norm_factor_eq_p p hp2 hpr d e he
  · -- d non-unit
    intro hdunit
    obtain ⟨cc, hcc⟩ := dvd_conj_of_gcd_unit p k x d s t hbez hdunit hk
    exact not_dvd_unit_im (p : Int) (⟨x, -1⟩ : ZOmega).conj hp1 (Or.inl rfl) ⟨cc, hcc⟩
  · -- e non-unit
    intro heunit
    have hec : e * e.conj = ZOmega.ofInt 1 := unit_of_normSq_one e heunit
    have hd_eq : d = ZOmega.ofInt (p : Int) * e.conj := by
      calc d = d * ZOmega.ofInt 1 := (mul_ofInt_one d).symm
        _ = d * (e * e.conj) := by rw [hec]
        _ = (d * e) * e.conj := by rw [← mul_assoc]
        _ = ZOmega.ofInt (p : Int) * e.conj := by rw [← he]
    obtain ⟨m, hm⟩ := hdω
    apply not_dvd_unit_im (p : Int) (⟨x, -1⟩ : ZOmega) hp1 (Or.inr rfl)
    exact ⟨e.conj * m, by rw [hm, hd_eq, mul_assoc]⟩

/-- ★★★★ **The Eisenstein split, form level.**  `p` prime, `p ∣ x²+x+1`, `¬(p:ℤ)∣1` ⟹
    `p = a² − ab + b²` for some integers `a, b` (the real-part/imaginary-part of the norm-`p`
    element).  The disc-`−3` Fermat representation, given the primitive-cube-root input. -/
theorem split_form (p : Nat) (hp2 : 2 ≤ p) (hpr : ∀ m, m ∣ p → m = 1 ∨ m = p)
    (hp1 : ¬ ((p : Int) ∣ (1 : Int))) (x : Int) (hx : (p : Int) ∣ (x * x + x + 1)) :
    ∃ a b : Int, (p : Int) = a * a - a * b + b * b := by
  obtain ⟨d, hd⟩ := split_norm p hp2 hpr hp1 x hx
  exact ⟨d.re, d.im, hd.symm⟩

end E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinSplit
