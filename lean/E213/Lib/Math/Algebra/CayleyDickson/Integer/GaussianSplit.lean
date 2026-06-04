import E213.Lib.Math.Algebra.CayleyDickson.Integer.GaussianGcd
import E213.Lib.Math.Algebra.CayleyDickson.Integer.GaussianDvd
import E213.Lib.Math.NumberTheory.ModArith.PrimeSquareFactor
import E213.Meta.Int213.OrderMul

/-!
# GaussianSplit — Euclid's lemma in `ℤ[i]` and the split-prime norm (Gaussian Phase 2c)

Disc-`−4` analog of `EisensteinSplit`.  Given `p` prime with `p ∣ x² + 1`, the element
`x − i = ⟨x, −1⟩` satisfies `(x−i)·conj(x−i) = ofInt(x²+1)`, so `ofInt p ∣ (x−i)·conj(x−i)`
while `ofInt p ∤ (x−i)` and `ofInt p ∤ conj(x−i)` (both have a unit imaginary part).  The
Euclidean gcd `d = gcd(ofInt p, x−i)` is a proper non-unit divisor, so `ofInt p = d·e` with
`p² = ‖d‖²·‖e‖²`, both `≥ 2`, hence `‖d‖² = p` — i.e. `p = a² + b²`.

  * ★★★★ `split_norm` / `split_form` — `p ∣ x²+1` ⟹ `∃ d, ‖d‖² = p` (`p = a² + b²`).

All zero-axiom.
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.GaussianSplit

open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZI (ZI)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZI.ZI
open E213.Lib.Math.Algebra.CayleyDickson.Integer.GaussianDivStep (normSq_pos)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.GaussianDvd
  (mul_conj_self normSq_dvd_of_dvd unit_of_normSq_one normSq_one_of_unit dvd_components_of_dvd
   normSq_x_sub_i)
open E213.Lib.Math.NumberTheory.ModArith.PrimeSquareFactor (eq_p_of_mul_eq_psq)
open E213.Meta.Int213.OrderMul (natAbs_cast_of_nonneg)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.GaussianGcd
  (gcd_bezout ofInt_one_mul mul_ofInt_one)
open E213.Meta.Algebra213 (CommRing213)
open E213.Meta.Algebra213.Ring213 (add_mul mul_add)
open E213.Meta.Algebra213.Ring213 renaming mul_assoc → rmul_assoc
open E213.Meta.Algebra213.CommRing213 renaming mul_comm → zmul_comm

/-! ## §1 — `ofInt` is multiplicative, and its norm -/

theorem ofInt_mul (a b : Int) : ZI.ofInt (a * b) = ZI.ofInt a * ZI.ofInt b := by
  refine ZI.ext ?_ ?_
  · show a * b = a * b - 0 * 0
    rw [E213.Meta.Int213.zero_mul, E213.Meta.Int213.Order.sub_zero]
  · show (0 : Int) = a * 0 + 0 * b
    rw [E213.Meta.Int213.PolyIntM.mul_zeroZ, E213.Meta.Int213.zero_mul,
        E213.Meta.Int213.zero_add]

theorem ofInt_normSq (n : Int) : (ZI.ofInt n).normSq = n * n := by
  show n * n + 0 * 0 = n * n
  rw [E213.Meta.Int213.zero_mul, Int.add_zero]

/-! ## §2 — the cyclotomic factorization -/

/-- `⟨x,−1⟩ · conj⟨x,−1⟩ = ofInt (x² + 1)`. -/
theorem cyclotomic_factor (x : Int) :
    (⟨x, -1⟩ : ZI) * ZI.conj (⟨x, -1⟩ : ZI) = ZI.ofInt (x * x + 1) := by
  rw [mul_conj_self, normSq_x_sub_i]

/-! ## §3 — a non-unit does not divide an element with unit imaginary part -/

theorem not_dvd_unit_im (p : Int) (θ : ZI) (hp : ¬ (p ∣ (1 : Int)))
    (him : θ.im = 1 ∨ θ.im = -1) : ¬ ∃ c : ZI, θ = ZI.ofInt p * c := by
  intro hd
  obtain ⟨c, hc⟩ := hd
  have hpim : p ∣ θ.im := (dvd_components_of_dvd p θ c hc).2
  rcases him with h1 | h1
  · rw [h1] at hpim; exact hp hpim
  · rw [h1] at hpim
    obtain ⟨k, hk⟩ := hpim
    exact hp ⟨-k, by rw [E213.Meta.Int213.mul_neg, ← hk, Int.neg_neg]⟩

/-! ## §3b — the unit-Bezout ⟹ `p ∣ conj(x−i)` engine -/

theorem mul_right_comm213 {α} [CommRing213 α] (a b c : α) : a * b * c = a * c * b := by
  rw [rmul_assoc, zmul_comm b c, ← rmul_assoc]

theorem unit_bezout_dvd_conj (p k x : Int) (s t : ZI)
    (hu : ZI.ofInt 1 = s * ZI.ofInt p + t * (⟨x, -1⟩ : ZI))
    (hk : x * x + 1 = p * k) :
    ∃ c : ZI, ZI.conj (⟨x, -1⟩ : ZI) = ZI.ofInt p * c := by
  refine ⟨s * ZI.conj (⟨x, -1⟩ : ZI) + t * ZI.ofInt k, ?_⟩
  have e1 : (s * ZI.ofInt p) * ZI.conj (⟨x, -1⟩ : ZI)
          = ZI.ofInt p * (s * ZI.conj (⟨x, -1⟩ : ZI)) := by
    rw [zmul_comm s (ZI.ofInt p), mul_assoc]
  have e2 : t * (ZI.ofInt p * ZI.ofInt k) = ZI.ofInt p * (t * ZI.ofInt k) := by
    rw [← mul_assoc, zmul_comm t (ZI.ofInt p), mul_assoc]
  calc ZI.conj (⟨x, -1⟩ : ZI)
      = ZI.ofInt 1 * ZI.conj (⟨x, -1⟩ : ZI) := (ofInt_one_mul _).symm
    _ = (s * ZI.ofInt p + t * ⟨x, -1⟩) * ZI.conj (⟨x, -1⟩ : ZI) := by rw [hu]
    _ = (s * ZI.ofInt p) * ZI.conj (⟨x, -1⟩ : ZI)
          + (t * ⟨x, -1⟩) * ZI.conj (⟨x, -1⟩ : ZI) := by rw [add_mul]
    _ = (s * ZI.ofInt p) * ZI.conj (⟨x, -1⟩ : ZI)
          + t * ((⟨x, -1⟩ : ZI) * ZI.conj (⟨x, -1⟩ : ZI)) := by
        rw [mul_assoc t (⟨x, -1⟩ : ZI) (ZI.conj (⟨x, -1⟩ : ZI))]
    _ = (s * ZI.ofInt p) * ZI.conj (⟨x, -1⟩ : ZI)
          + t * (ZI.ofInt p * ZI.ofInt k) := by rw [cyclotomic_factor, hk, ofInt_mul]
    _ = ZI.ofInt p * (s * ZI.conj (⟨x, -1⟩ : ZI))
          + ZI.ofInt p * (t * ZI.ofInt k) := by rw [e1, e2]
    _ = ZI.ofInt p * (s * ZI.conj (⟨x, -1⟩ : ZI) + t * ZI.ofInt k) := by rw [← mul_add]

theorem dvd_conj_of_gcd_unit (p k x : Int) (d s t : ZI)
    (hbez : d = s * ZI.ofInt p + t * (⟨x, -1⟩ : ZI)) (hdunit : d.normSq = 1)
    (hk : x * x + 1 = p * k) :
    ∃ c : ZI, ZI.conj (⟨x, -1⟩ : ZI) = ZI.ofInt p * c := by
  have hdc : d * ZI.conj d = ZI.ofInt 1 := unit_of_normSq_one d hdunit
  have hsb : (s * ZI.ofInt p + t * (⟨x, -1⟩ : ZI)) * ZI.conj d = ZI.ofInt 1 := by
    rw [← hbez]; exact hdc
  have hbez1 : ZI.ofInt 1
      = (s * ZI.conj d) * ZI.ofInt p + (t * ZI.conj d) * (⟨x, -1⟩ : ZI) := by
    rw [← hsb, add_mul, mul_right_comm213 s (ZI.ofInt p) (ZI.conj d),
        mul_right_comm213 t (⟨x, -1⟩ : ZI) (ZI.conj d)]
  exact unit_bezout_dvd_conj p k x (s * ZI.conj d) (t * ZI.conj d) hbez1 hk

/-! ## §4 — a non-unit factorization of `ofInt p` has a norm-`p` factor -/

theorem norm_factor_eq_p (p : Nat) (hp2 : 2 ≤ p) (hpr : ∀ m, m ∣ p → m = 1 ∨ m = p)
    (d e : ZI) (he : ZI.ofInt (p : Int) = d * e)
    (hd1 : d.normSq ≠ 1) (he1 : e.normSq ≠ 1) : d.normSq = (p : Int) := by
  have hPne : ZI.ofInt (p : Int) ≠ 0 := by
    intro h
    have hpr0 : (p : Int) = 0 := congrArg ZI.re h
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
  have hprod : d.normSq * e.normSq = (p : Int) * (p : Int) := by
    rw [← normSq_mul, ← he, ofInt_normSq]
  have hprodN : d.normSq.natAbs * e.normSq.natAbs = p * p := by
    have hcast : ((d.normSq.natAbs * e.normSq.natAbs : Nat) : Int) = ((p * p : Nat) : Int) := by
      rw [Int.ofNat_mul, hndc, hnec, hprod, Int.ofNat_mul]
    exact Int.ofNat.inj hcast
  have hkey : ∀ m : Nat, m ≠ 0 → m ≠ 1 → 2 ≤ m := by
    intro m hm0 hm1
    rcases m with _ | _ | k
    · exact absurd rfl hm0
    · exact absurd rfl hm1
    · exact Nat.le_add_left 2 k
  have hge2 : ∀ (q : ZI), 0 < q.normSq → q.normSq ≠ 1 → 2 ≤ q.normSq.natAbs := by
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
  have hpow : d.normSq.natAbs * e.normSq.natAbs = p ^ 2 := by
    rw [hprodN, Nat.pow_succ, Nat.pow_one]
  have hnd : d.normSq.natAbs = p :=
    eq_p_of_mul_eq_psq p d.normSq.natAbs e.normSq.natAbs hp2 hpr hndge hnege hpow
  rw [← hndc, hnd]

/-! ## §5 — the split -/

/-- ★★★★ **The Gaussian split.**  `p` prime, `p ∣ x² + 1`, `¬(p:ℤ)∣1` ⟹ `∃ d, ‖d‖² = p`. -/
theorem split_norm (p : Nat) (hp2 : 2 ≤ p) (hpr : ∀ m, m ∣ p → m = 1 ∨ m = p)
    (hp1 : ¬ ((p : Int) ∣ (1 : Int)))
    (x : Int) (hx : (p : Int) ∣ (x * x + 1)) :
    ∃ d : ZI, d.normSq = (p : Int) := by
  obtain ⟨k, hk⟩ := hx
  obtain ⟨d, s, t, hbez, hdP, hdω⟩ :=
    gcd_bezout (⟨x, -1⟩ : ZI).normSq.natAbs (ZI.ofInt (p : Int)) (⟨x, -1⟩ : ZI) (Nat.le_refl _)
  obtain ⟨e, he⟩ := hdP
  refine ⟨d, ?_⟩
  apply norm_factor_eq_p p hp2 hpr d e he
  · intro hdunit
    obtain ⟨cc, hcc⟩ := dvd_conj_of_gcd_unit p k x d s t hbez hdunit hk
    exact not_dvd_unit_im (p : Int) (ZI.conj (⟨x, -1⟩ : ZI)) hp1 (Or.inl rfl) ⟨cc, hcc⟩
  · intro heunit
    have hec : e * ZI.conj e = ZI.ofInt 1 := unit_of_normSq_one e heunit
    have hd_eq : d = ZI.ofInt (p : Int) * ZI.conj e := by
      calc d = d * ZI.ofInt 1 := (mul_ofInt_one d).symm
        _ = d * (e * ZI.conj e) := by rw [hec]
        _ = (d * e) * ZI.conj e := by rw [← mul_assoc]
        _ = ZI.ofInt (p : Int) * ZI.conj e := by rw [← he]
    obtain ⟨m, hm⟩ := hdω
    apply not_dvd_unit_im (p : Int) (⟨x, -1⟩ : ZI) hp1 (Or.inr rfl)
    exact ⟨ZI.conj e * m, by rw [hm, hd_eq, mul_assoc]⟩

/-- ★★★★ **The Gaussian two-square split, form level.**  `p` prime, `p ∣ x²+1`, `¬(p:ℤ)∣1` ⟹
    `p = a² + b²` for some integers `a, b` (`= ‖d‖²` for the norm-`p` element). -/
theorem split_form (p : Nat) (hp2 : 2 ≤ p) (hpr : ∀ m, m ∣ p → m = 1 ∨ m = p)
    (hp1 : ¬ ((p : Int) ∣ (1 : Int))) (x : Int) (hx : (p : Int) ∣ (x * x + 1)) :
    ∃ a b : Int, (p : Int) = a * a + b * b := by
  obtain ⟨d, hd⟩ := split_norm p hp2 hpr hp1 x hx
  exact ⟨d.re, d.im, hd.symm⟩

end E213.Lib.Math.Algebra.CayleyDickson.Integer.GaussianSplit
