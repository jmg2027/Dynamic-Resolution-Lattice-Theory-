import E213.Lib.Math.NumberSystems.Real213.ContinuedFraction.ContinuantDeterminant
import E213.Meta.Int213.Core

/-!
# Coprimality of consecutive continued-fraction convergents (∅-axiom)

From the unit cross-determinant `M.a·M.d − M.b·M.c = ±1` (Euler's continuant
identity, `ContinuantDeterminant.continuant_det_unit`) we derive that the
`(1,1)`- and `(2,1)`-entries of the continuant matrix product are **coprime**:
any common divisor of `M.a` (= `K[a₁..aₙ]`) and `M.c` (= `K[a₂..aₙ]`) divides
`±1`, hence is a unit.

This is the classical fact that the convergents `pₙ/qₙ` of a continued fraction
are in lowest terms (`gcd(pₙ,qₙ) = 1`) — the foundational property underwriting
CF approximation theory.

`Int213` carries no `∣`-infrastructure, so the four local divisibility helpers
(`dvd_subZ`, `dvd_mul_rightZ`, `dvd_mul_leftZ`, `dvd_one_of_dvd_negOneZ`) are
proven PURE here via explicit witnesses + `ring_intZ`.  All ∅-axiom.
-/

namespace E213.Lib.Math.NumberSystems.Real213.ContinuedFraction.ConvergentCoprime

open E213.Lib.Math.NumberSystems.Real213.ModularGeometry.ModularElliptic (Mat2)
open E213.Lib.Math.NumberSystems.Real213.ContinuedFraction.Continuant (contMatProd)
open E213.Lib.Math.NumberSystems.Real213.ContinuedFraction.ContinuantDeterminant
  (continuant_det_unit)

/-- **`dvd_sub` for `Int`** (PURE, via explicit witness + `ring_intZ`).
    If `g ∣ x` and `g ∣ y` then `g ∣ (x − y)`. -/
theorem dvd_subZ {g x y : Int} (hx : g ∣ x) (hy : g ∣ y) : g ∣ (x - y) := by
  obtain ⟨w₁, hw₁⟩ := hx
  obtain ⟨w₂, hw₂⟩ := hy
  refine ⟨w₁ - w₂, ?_⟩
  rw [hw₁, hw₂]
  show g * w₁ - g * w₂ = g * (w₁ - w₂)
  exact (E213.Meta.Int213.mul_sub g w₁ w₂).symm

/-- `g ∣ x → g ∣ (x * d)` for `Int` (PURE, witness `w * d` + `ring_intZ`). -/
theorem dvd_mul_rightZ {g x : Int} (d : Int) (hx : g ∣ x) : g ∣ (x * d) := by
  obtain ⟨w, hw⟩ := hx
  refine ⟨w * d, ?_⟩
  rw [hw]
  show g * w * d = g * (w * d)
  ring_intZ

/-- `g ∣ y → g ∣ (b * y)` for `Int` (PURE, witness `b * w` + `ring_intZ`). -/
theorem dvd_mul_leftZ {g y : Int} (b : Int) (hy : g ∣ y) : g ∣ (b * y) := by
  obtain ⟨w, hw⟩ := hy
  refine ⟨b * w, ?_⟩
  rw [hw]
  show b * (g * w) = g * (b * w)
  ring_intZ

/-- `g ∣ (-1) → g ∣ 1` for `Int` (PURE, negate the witness + `ring_intZ`). -/
theorem dvd_one_of_dvd_negOneZ {g : Int} (h : g ∣ (-1 : Int)) : g ∣ (1 : Int) := by
  obtain ⟨w, hw⟩ := h
  refine ⟨-w, ?_⟩
  show (1 : Int) = g * (-w)
  have hw' : (-1 : Int) = g * w := hw
  -- from -1 = g*w, get 1 = -(g*w) = g*(-w)
  calc (1 : Int) = -(-1) := by ring_intZ
    _ = -(g * w) := by rw [hw']
    _ = g * (-w) := by ring_intZ

/-- ★ **Coprimality of the continuant cross-pair** (∅-axiom).
    Any common divisor `g` of the `(1,1)`-entry `M.a` and the `(2,1)`-entry `M.c`
    of the continuant matrix product `M = ∏ᵢ [[aᵢ,1],[1,0]]` divides `1`, i.e. is a unit.

    Mathematically: consecutive convergents `pₙ/qₙ` are in lowest terms,
    `gcd(pₙ, qₙ) = 1`.  Proof: `g ∣ a ⟹ g ∣ a·d`, `g ∣ c ⟹ g ∣ b·c`, so
    `g ∣ (a·d − b·c) = ±1` (Euler's `continuant_det_unit`), hence `g ∣ 1`. -/
theorem continuant_coprime (l : List Nat) (g : Int)
    (ha : g ∣ (contMatProd l).a) (hc : g ∣ (contMatProd l).c) :
    g ∣ (1 : Int) := by
  -- g divides a*d
  have had : g ∣ (contMatProd l).a * (contMatProd l).d := dvd_mul_rightZ _ ha
  -- g divides b*c
  have hbc : g ∣ (contMatProd l).b * (contMatProd l).c := dvd_mul_leftZ _ hc
  -- g divides the cross-determinant a*d - b*c
  have hdet : g ∣ ((contMatProd l).a * (contMatProd l).d
                    - (contMatProd l).b * (contMatProd l).c) := dvd_subZ had hbc
  -- the cross-determinant is ±1
  cases continuant_det_unit l with
  | inl h1 =>
      -- = 1
      have : g ∣ (1 : Int) := by rw [h1] at hdet; exact hdet
      exact this
  | inr hm1 =>
      -- = -1
      have hneg : g ∣ (-1 : Int) := by rw [hm1] at hdet; exact hdet
      exact dvd_one_of_dvd_negOneZ hneg

end E213.Lib.Math.NumberSystems.Real213.ContinuedFraction.ConvergentCoprime
