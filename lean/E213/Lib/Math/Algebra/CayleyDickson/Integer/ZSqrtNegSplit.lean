import E213.Lib.Math.Algebra.CayleyDickson.Integer.ZSqrtNegDivStep
import E213.Lib.Math.NumberTheory.ModArith.PrimeSquareFactor
import E213.Meta.Int213.OrderMul
import E213.Meta.Algebra213.Core

/-!
# ZSqrtNegSplit — divisibility, gcd, and the split-prime norm in `ℤ[√−D]` (parametric)

The parametric disc-`−D` descent (`1 ≤ D ≤ 2`), generalising `GaussianDvd`/`GaussianGcd`/
`GaussianSplit` over the radicand.  With `ℤ[√−D]` norm-Euclidean
(`ZSqrtNegDivStep.zsqrt_div_step`):

  * `Dvd (ZSqrt D)`, `zdvd_combo`, `gcd_bezout` — Euclidean gcd + Bezout (fuel induction).
  * `normSq_x_sub_root` — `‖x − √−D‖² = x² + D`.
  * ★★★★ `split_form` — `p` prime, `p ∣ x² + D`, `¬(p:ℤ)∣1` ⟹ `∃ a b : Int, ↑p = a² + D·b²`.

Instantiating `D = 1` recovers the Gaussian two-square split; `D = 2` gives `p = a² + 2b²`.

All zero-axiom.
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.ZSqrtNegSplit

open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZSqrt (ZSqrt ofInt)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZSqrt.ZSqrt
open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZSqrtNegDivStep (zsqrt_div_step normSq_pos)
open E213.Lib.Math.NumberTheory.ModArith.PrimeSquareFactor (eq_p_of_mul_eq_psq)
open E213.Meta.Int213.OrderMul (natAbs_lt_of_lt natAbs_cast_of_nonneg)
open E213.Meta.Algebra213 (Ring213 CommRing213)
open E213.Meta.Algebra213.Ring213
  (add_mul mul_add neg_mul add_4_swap_mid neg_add_cancel_self add_comm add_zero mul_zero)
open E213.Meta.Algebra213.Ring213 renaming mul_assoc → rmul_assoc
open E213.Meta.Algebra213.CommRing213 renaming mul_comm → zmul_comm
open E213.Meta.Int213 (zero_mul mul_one mul_neg)
open E213.Meta.Int213 renaming zero_add → int_zero_add, add_comm → int_add_comm
open E213.Meta.Int213.Order (sub_zero le_of_lt lt_of_le_of_lt lt_of_lt_of_le)
open E213.Meta.Int213.PolyIntM (one_mulZ mul_zeroZ)

/-! ## §1 — divisibility↔norm helpers -/

theorem mul_conj_self {D : Int} (u : ZSqrt D) : u * ZSqrt.conj u = ofInt D u.normSq := by
  cases u with
  | mk p q =>
    refine ZSqrt.ext ?_ ?_
    · show p * p - D * (q * (-q)) = p * p + D * (q * q)
      ring_intZ
    · show p * (-q) + q * p = 0
      have hz : p * (-q) + q * p = q * q - q * q := by ring_intZ
      rw [hz, E213.Meta.Int213.Order.sub_self_zero]

theorem normSq_dvd_of_dvd {D : Int} (a b c : ZSqrt D) (hc : b = a * c) : a.normSq ∣ b.normSq := by
  rw [hc, normSq_mul]; exact ⟨c.normSq, rfl⟩

theorem unit_of_normSq_one {D : Int} (u : ZSqrt D) (h : u.normSq = 1) :
    u * ZSqrt.conj u = ofInt D 1 := by rw [mul_conj_self, h]

private theorem nat_eq_one_of_mul (n m : Nat) (h : n * m = 1) : n = 1 := by
  cases n with
  | zero => rw [Nat.zero_mul] at h; exact absurd h (by decide)
  | succ k =>
    cases k with
    | zero => rfl
    | succ j =>
      exfalso
      cases m with
      | zero => rw [Nat.mul_zero] at h; exact absurd h (by decide)
      | succ i =>
        have h2 : 2 ≤ (j + 2) * (i + 1) :=
          Nat.le_trans (by decide : 2 ≤ 2 * 1)
            (Nat.mul_le_mul (Nat.le_add_left 2 j) (Nat.succ_le_succ (Nat.zero_le i)))
        rw [h] at h2; exact absurd h2 (by decide)

private theorem int_mul_eq_one_nonneg {a b : Int} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (h : a * b = 1) : a = 1 := by
  cases a with
  | ofNat n =>
    cases b with
    | ofNat m =>
      have hnm : n * m = 1 := Int.ofNat.inj ((Int.ofNat_mul n m).trans h)
      rw [nat_eq_one_of_mul n m hnm]; rfl
    | negSucc m => exact absurd hb (by intro hc; cases hc)
  | negSucc n => exact absurd ha (by intro hc; cases hc)

/-- `(0 : ZSqrt D).normSq = 0` (for `0 < D`, via `normSq_eq_zero_iff`). -/
theorem normSq_zero {D : Int} (hDpos : 0 < D) : (0 : ZSqrt D).normSq = 0 :=
  (normSq_eq_zero_iff hDpos 0).mpr rfl

theorem dvd_components_of_dvd {D : Int} (p : Int) (θ c : ZSqrt D) (h : θ = ofInt D p * c) :
    (p ∣ θ.re) ∧ (p ∣ θ.im) := by
  have hre : θ.re = p * c.re := by
    rw [h]
    show p * c.re - D * (0 * c.im) = p * c.re
    rw [zero_mul, mul_zeroZ, sub_zero]
  have him : θ.im = p * c.im := by
    rw [h]
    show p * c.im + 0 * c.re = p * c.im
    rw [zero_mul, Int.add_zero]
  exact ⟨⟨c.re, hre⟩, ⟨c.im, him⟩⟩

/-- `‖x − √−D‖² = x² + D`. -/
theorem normSq_x_sub_root (D x : Int) : (⟨x, -1⟩ : ZSqrt D).normSq = x * x + D := by
  show x * x + D * ((-1) * (-1)) = x * x + D
  ring_intZ

theorem not_dvd_unit_im {D : Int} (p : Int) (θ : ZSqrt D) (hp : ¬ (p ∣ (1 : Int)))
    (him : θ.im = 1 ∨ θ.im = -1) : ¬ ∃ c : ZSqrt D, θ = ofInt D p * c := by
  intro hd
  obtain ⟨c, hc⟩ := hd
  have hpim : p ∣ θ.im := (dvd_components_of_dvd p θ c hc).2
  rcases him with h1 | h1
  · rw [h1] at hpim; exact hp hpim
  · rw [h1] at hpim
    obtain ⟨k, hk⟩ := hpim
    exact hp ⟨-k, by rw [mul_neg, ← hk, Int.neg_neg]⟩

/-! ## §2 — `Dvd`, closure, `ofInt`-unit algebra -/

instance {D : Int} : Dvd (ZSqrt D) := ⟨fun a b => ∃ c, b = a * c⟩

theorem zdvd_combo {D : Int} {d α β γ ρ : ZSqrt D} (hβ : d ∣ β) (hρ : d ∣ ρ)
    (hα : α = β * γ + ρ) : d ∣ α := by
  obtain ⟨b, hb⟩ := hβ
  obtain ⟨c, hc⟩ := hρ
  exact ⟨b * γ + c, by rw [hα, hb, hc, rmul_assoc, ← mul_add]⟩

theorem ofInt_one_mul {D : Int} (a : ZSqrt D) : ofInt D 1 * a = a := by
  refine ZSqrt.ext ?_ ?_
  · show (1 : Int) * a.re - D * (0 * a.im) = a.re
    rw [zero_mul, mul_zeroZ, sub_zero, one_mulZ]
  · show (1 : Int) * a.im + 0 * a.re = a.im
    rw [zero_mul, Int.add_zero, one_mulZ]

theorem mul_ofInt_one {D : Int} (a : ZSqrt D) : a * ofInt D 1 = a := by
  refine ZSqrt.ext ?_ ?_
  · show a.re * 1 - D * (a.im * 0) = a.re
    rw [mul_zeroZ, mul_zeroZ, sub_zero, mul_one]
  · show a.re * 0 + a.im * 1 = a.im
    rw [mul_zeroZ, int_zero_add, mul_one]

theorem zdvd_refl {D : Int} (a : ZSqrt D) : a ∣ a := ⟨ofInt D 1, (mul_ofInt_one a).symm⟩

theorem zdvd_zero {D : Int} (a : ZSqrt D) : a ∣ (0 : ZSqrt D) := ⟨ofInt D 0, (mul_zero a).symm⟩

/-! ## §3 — Bezout rearrangement + fuel-induction gcd -/

theorem rearrange_helper {α} [Ring213 α] (A B S : α) : A + B + (S + -A) = S + B := by
  rw [add_comm S (-A), add_4_swap_mid A B (-A) S, add_comm A (-A), neg_add_cancel_self,
      E213.Meta.Algebra213.Ring213.zero_add, add_comm B S]

theorem bezout_rearrange {D : Int} (s t β ρ γ : ZSqrt D) :
    t * (β * γ + ρ) + (s - t * γ) * β = s * β + t * ρ := by
  show t * (β * γ + ρ) + (s + -(t * γ)) * β = s * β + t * ρ
  have h1 : (s + -(t * γ)) * β = s * β + -(t * (β * γ)) := by
    rw [add_mul, neg_mul, rmul_assoc, zmul_comm γ β]
  rw [mul_add, h1]
  exact rearrange_helper (t * (β * γ)) (t * ρ) (s * β)

theorem normSq_natAbs_zero {D : Int} (hDpos : 0 < D) {β : ZSqrt D} (h : β.normSq.natAbs = 0) :
    β = 0 := by
  have hz : β.normSq = 0 := by
    have hc := natAbs_cast_of_nonneg (normSq_nonneg (le_of_lt hDpos) β)
    rw [h] at hc; exact hc.symm
  exact (normSq_eq_zero_iff hDpos β).mp hz

/-- ★★★★ **The `ℤ[√−D]` Euclidean gcd + Bezout** (`1 ≤ D ≤ 2`). -/
theorem gcd_bezout {D : Int} (hD1 : 1 ≤ D) (hD2 : D ≤ 2) :
    ∀ (n : Nat) (α β : ZSqrt D), β.normSq.natAbs ≤ n →
      ∃ d s t : ZSqrt D, d = s * α + t * β ∧ (d ∣ α) ∧ (d ∣ β) := by
  have hDpos : 0 < D := lt_of_lt_of_le (show (0:Int) < 1 by decide) hD1
  intro n
  induction n with
  | zero =>
    intro α β hβ
    have hβ0 : β = 0 := normSq_natAbs_zero hDpos (Nat.le_zero.mp hβ)
    refine ⟨α, ofInt D 1, ofInt D 0, ?_, zdvd_refl α, by rw [hβ0]; exact zdvd_zero α⟩
    rw [hβ0, ofInt_one_mul, mul_zero, add_zero]
  | succ n ih =>
    intro α β hβ
    rcases Nat.eq_zero_or_pos β.normSq.natAbs with h0 | hpos
    · have hβ0 : β = 0 := normSq_natAbs_zero hDpos h0
      refine ⟨α, ofInt D 1, ofInt D 0, ?_, zdvd_refl α, by rw [hβ0]; exact zdvd_zero α⟩
      rw [hβ0, ofInt_one_mul, mul_zero, add_zero]
    · have hβne : β ≠ 0 := by
        intro h; rw [h, normSq_zero hDpos] at hpos; exact absurd hpos (Nat.lt_irrefl 0)
      obtain ⟨γ, ρ, hα, hρ⟩ := zsqrt_div_step hD1 hD2 α β hβne
      have hfuel : ρ.normSq.natAbs ≤ n :=
        Nat.le_of_lt_succ (Nat.lt_of_lt_of_le (natAbs_lt_of_lt (normSq_nonneg (le_of_lt hDpos) ρ) hρ) hβ)
      obtain ⟨d, s, t, hd, hdβ, hdρ⟩ := ih β ρ hfuel
      have hdα : d ∣ α := zdvd_combo hdβ hdρ hα
      refine ⟨d, t, s - t * γ, ?_, hdα, hdβ⟩
      rw [hd, hα]
      exact (bezout_rearrange s t β ρ γ).symm

/-! ## §4 — split setup + the split -/

theorem ofInt_mul {D : Int} (a b : Int) :
    (ofInt D (a * b) : ZSqrt D) = ofInt D a * ofInt D b := by
  refine ZSqrt.ext ?_ ?_
  · show a * b = a * b - D * (0 * 0)
    rw [zero_mul, mul_zeroZ, sub_zero]
  · show (0 : Int) = a * 0 + 0 * b
    rw [mul_zeroZ, zero_mul, int_zero_add]

theorem ofInt_normSq {D : Int} (n : Int) : (ofInt D n : ZSqrt D).normSq = n * n := by
  show n * n + D * (0 * 0) = n * n
  rw [zero_mul, mul_zeroZ, Int.add_zero]

theorem cyclotomic_factor (D x : Int) :
    (⟨x, -1⟩ : ZSqrt D) * ZSqrt.conj (⟨x, -1⟩ : ZSqrt D) = ofInt D (x * x + D) := by
  rw [mul_conj_self, normSq_x_sub_root]

theorem mul_right_comm213 {α} [CommRing213 α] (a b c : α) : a * b * c = a * c * b := by
  rw [rmul_assoc, zmul_comm b c, ← rmul_assoc]

theorem unit_bezout_dvd_conj {D : Int} (p k x : Int) (s t : ZSqrt D)
    (hu : ofInt D 1 = s * ofInt D p + t * (⟨x, -1⟩ : ZSqrt D))
    (hk : x * x + D = p * k) :
    ∃ c : ZSqrt D, ZSqrt.conj (⟨x, -1⟩ : ZSqrt D) = ofInt D p * c := by
  refine ⟨s * ZSqrt.conj (⟨x, -1⟩ : ZSqrt D) + t * ofInt D k, ?_⟩
  have e1 : (s * ofInt D p) * ZSqrt.conj (⟨x, -1⟩ : ZSqrt D)
          = ofInt D p * (s * ZSqrt.conj (⟨x, -1⟩ : ZSqrt D)) := by
    rw [zmul_comm s (ofInt D p), rmul_assoc]
  have e2 : t * (ofInt D p * ofInt D k) = ofInt D p * (t * ofInt D k) := by
    rw [← rmul_assoc, zmul_comm t (ofInt D p), rmul_assoc]
  calc ZSqrt.conj (⟨x, -1⟩ : ZSqrt D)
      = ofInt D 1 * ZSqrt.conj (⟨x, -1⟩ : ZSqrt D) := (ofInt_one_mul _).symm
    _ = (s * ofInt D p + t * ⟨x, -1⟩) * ZSqrt.conj (⟨x, -1⟩ : ZSqrt D) := by rw [hu]
    _ = (s * ofInt D p) * ZSqrt.conj (⟨x, -1⟩ : ZSqrt D)
          + (t * ⟨x, -1⟩) * ZSqrt.conj (⟨x, -1⟩ : ZSqrt D) := by rw [add_mul]
    _ = (s * ofInt D p) * ZSqrt.conj (⟨x, -1⟩ : ZSqrt D)
          + t * ((⟨x, -1⟩ : ZSqrt D) * ZSqrt.conj (⟨x, -1⟩ : ZSqrt D)) := by
        rw [rmul_assoc t (⟨x, -1⟩ : ZSqrt D) (ZSqrt.conj (⟨x, -1⟩ : ZSqrt D))]
    _ = (s * ofInt D p) * ZSqrt.conj (⟨x, -1⟩ : ZSqrt D)
          + t * (ofInt D p * ofInt D k) := by rw [cyclotomic_factor, hk, ofInt_mul]
    _ = ofInt D p * (s * ZSqrt.conj (⟨x, -1⟩ : ZSqrt D))
          + ofInt D p * (t * ofInt D k) := by rw [e1, e2]
    _ = ofInt D p * (s * ZSqrt.conj (⟨x, -1⟩ : ZSqrt D) + t * ofInt D k) := by rw [← mul_add]

theorem dvd_conj_of_gcd_unit {D : Int} (p k x : Int) (d s t : ZSqrt D)
    (hbez : d = s * ofInt D p + t * (⟨x, -1⟩ : ZSqrt D)) (hdunit : d.normSq = 1)
    (hk : x * x + D = p * k) :
    ∃ c : ZSqrt D, ZSqrt.conj (⟨x, -1⟩ : ZSqrt D) = ofInt D p * c := by
  have hdc : d * ZSqrt.conj d = ofInt D 1 := unit_of_normSq_one d hdunit
  have hsb : (s * ofInt D p + t * (⟨x, -1⟩ : ZSqrt D)) * ZSqrt.conj d = ofInt D 1 := by
    rw [← hbez]; exact hdc
  have hbez1 : ofInt D 1
      = (s * ZSqrt.conj d) * ofInt D p + (t * ZSqrt.conj d) * (⟨x, -1⟩ : ZSqrt D) := by
    rw [← hsb, add_mul, mul_right_comm213 s (ofInt D p) (ZSqrt.conj d),
        mul_right_comm213 t (⟨x, -1⟩ : ZSqrt D) (ZSqrt.conj d)]
  exact unit_bezout_dvd_conj p k x (s * ZSqrt.conj d) (t * ZSqrt.conj d) hbez1 hk

theorem norm_factor_eq_p {D : Int} (hDpos : 0 < D) (p : Nat) (hp2 : 2 ≤ p)
    (hpr : ∀ m, m ∣ p → m = 1 ∨ m = p)
    (d e : ZSqrt D) (he : ofInt D (p : Int) = d * e)
    (hd1 : d.normSq ≠ 1) (he1 : e.normSq ≠ 1) : d.normSq = (p : Int) := by
  have hPne : (ofInt D (p : Int) : ZSqrt D) ≠ 0 := by
    intro h
    have hpr0 : (p : Int) = 0 := congrArg ZSqrt.re h
    have : p = 0 := Int.ofNat.inj hpr0
    rw [this] at hp2; exact absurd hp2 (by decide)
  have hdne : d ≠ 0 := fun h => hPne (by rw [he, h]; exact E213.Meta.Algebra213.Ring213.zero_mul e)
  have hene : e ≠ 0 := fun h => hPne (by rw [he, h]; exact E213.Meta.Algebra213.Ring213.mul_zero d)
  have hdpos : 0 < d.normSq := normSq_pos hDpos d hdne
  have hepos : 0 < e.normSq := normSq_pos hDpos e hene
  have hndc : ((d.normSq.natAbs : Int)) = d.normSq := natAbs_cast_of_nonneg (le_of_lt hdpos)
  have hnec : ((e.normSq.natAbs : Int)) = e.normSq := natAbs_cast_of_nonneg (le_of_lt hepos)
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
  have hge2 : ∀ (q : ZSqrt D), 0 < q.normSq → q.normSq ≠ 1 → 2 ≤ q.normSq.natAbs := by
    intro q hqpos hq1
    have hqc : ((q.normSq.natAbs : Int)) = q.normSq := natAbs_cast_of_nonneg (le_of_lt hqpos)
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

/-- ★★★★ **The parametric split.**  `1 ≤ D ≤ 2`, `p` prime, `p ∣ x²+D`, `¬(p:ℤ)∣1` ⟹
    `∃ a b : Int, ↑p = a² + D·b²`. -/
theorem split_form {D : Int} (hD1 : 1 ≤ D) (hD2 : D ≤ 2) (p : Nat) (hp2 : 2 ≤ p)
    (hpr : ∀ m, m ∣ p → m = 1 ∨ m = p) (hp1 : ¬ ((p : Int) ∣ (1 : Int)))
    (x : Int) (hx : (p : Int) ∣ (x * x + D)) :
    ∃ a b : Int, (p : Int) = a * a + D * (b * b) := by
  have hDpos : 0 < D := lt_of_lt_of_le (show (0:Int) < 1 by decide) hD1
  obtain ⟨k, hk⟩ := hx
  obtain ⟨d, s, t, hbez, hdP, hdω⟩ :=
    gcd_bezout hD1 hD2 (⟨x, -1⟩ : ZSqrt D).normSq.natAbs (ofInt D (p : Int))
      (⟨x, -1⟩ : ZSqrt D) (Nat.le_refl _)
  obtain ⟨e, he⟩ := hdP
  have hnorm : d.normSq = (p : Int) := by
    apply norm_factor_eq_p hDpos p hp2 hpr d e he
    · intro hdunit
      obtain ⟨cc, hcc⟩ := dvd_conj_of_gcd_unit p k x d s t hbez hdunit hk
      exact not_dvd_unit_im (p : Int) (ZSqrt.conj (⟨x, -1⟩ : ZSqrt D)) hp1 (Or.inl rfl) ⟨cc, hcc⟩
    · intro heunit
      have hec : e * ZSqrt.conj e = ofInt D 1 := unit_of_normSq_one e heunit
      have hd_eq : d = ofInt D (p : Int) * ZSqrt.conj e := by
        calc d = d * ofInt D 1 := (mul_ofInt_one d).symm
          _ = d * (e * ZSqrt.conj e) := by rw [hec]
          _ = (d * e) * ZSqrt.conj e := by rw [← rmul_assoc]
          _ = ofInt D (p : Int) * ZSqrt.conj e := by rw [← he]
      obtain ⟨m, hm⟩ := hdω
      apply not_dvd_unit_im (p : Int) (⟨x, -1⟩ : ZSqrt D) hp1 (Or.inr rfl)
      exact ⟨ZSqrt.conj e * m, by rw [hm, hd_eq, rmul_assoc]⟩
  exact ⟨d.re, d.im, hnorm.symm⟩

/-- ★★★★ **`D = 2` instance.**  `p` prime, `p ∣ x² + 2`, `¬(p:ℤ)∣1` ⟹ `p = a² + 2b²`
    (the disc-`−8` split, in `ℤ[√−2]`).  `D = 1` recovers `GaussianSplit.split_form`. -/
theorem split_form_two (p : Nat) (hp2 : 2 ≤ p) (hpr : ∀ m, m ∣ p → m = 1 ∨ m = p)
    (hp1 : ¬ ((p : Int) ∣ (1 : Int))) (x : Int) (hx : (p : Int) ∣ (x * x + 2)) :
    ∃ a b : Int, (p : Int) = a * a + 2 * (b * b) :=
  split_form (D := 2) (by decide) (by decide) p hp2 hpr hp1 x hx

end E213.Lib.Math.Algebra.CayleyDickson.Integer.ZSqrtNegSplit
