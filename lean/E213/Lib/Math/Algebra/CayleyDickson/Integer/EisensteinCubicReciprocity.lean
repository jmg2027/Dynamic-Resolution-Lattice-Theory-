import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinConvGaussReindex
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinMu3Lift
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinInertCube
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicCharFp

/-!
# The cubic reciprocity law — `(π/q)₃ = χ(q)` as a well-defined `μ₃` equality (∅-axiom)

★★★★★ `cubic_reciprocity_law` : the capstone.  For a primary Jacobi prime `J = π` (norm `p`) and a
second rational prime `q ≡ 2 (mod 3)` (inert), the **cubic residue symbol** of `π` at `q`,

  `(π/q)₃  :=  the μ₃ value of  J^{(q²−1)/3}  mod q`,

is **well defined** and **equals** the cubic character value `χ(q) = (q/π)₃`.  Concretely the theorem
bundles three facts:

1. `χ(q) ∈ {1, ω, ω²}` — `χ(q)` is a genuine cube root of unity (`chiOmega_unit_value`);
2. `J^{(q²−1)/3} ≡ χ(q) (mod q)` — the reciprocity congruence (`cubic_reciprocity_power_congr`, the
   Gauss-sum Frobenius collapse);
3. **uniqueness/well-definedness**: *any* `μ₃` value `V` with `J^{(q²−1)/3} ≡ V (mod q)` equals `χ(q)`
   (`mu3_eq_of_modEq` — distinct cube roots stay distinct mod `q`).

Together: the residue symbol `(π/q)₃` is the single `μ₃` value `χ(q)`.  Existence of such a `V` is the
inert cube-splitting (`inert_cube_one_value`, since `J^{(q²−1)/3}` cubes to `1 mod q` — its cube is
`J^{q²−1} ≡ χ(q)³ = 1`).  `(π/q)₃ = χ(q) = (q/π)₃` is the cubic reciprocity relation; the `π ↔ π'`
symmetry then gives `(π/π')₃ = (π'/π)₃`.  ∅-axiom (PURE).
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicReciprocity

open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega (ZOmega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega.ZOmega (ofInt Omega Omega2 conj)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCongruence
  (ModEq trans symm mul_left mul_right)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinJacobiSum (jacobiSum)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.RootOfUnityOrthogonality (pow)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicCharFp (chiOmega chiOmega_unit_value)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinConvGaussReindex
  (cubic_reciprocity_power_congr)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinMu3Lift (mu3_eq_of_modEq)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinInertCube (inert_cube_one_value)
open E213.Tactic.NatHelper (gcd213)

/-- `ModEq` cubes a congruence: `a ≡ b ⟹ a·a·a ≡ b·b·b`. -/
private theorem modEq_cube {π a b : ZOmega} (h : ModEq π a b) :
    ModEq π (a * a * a) (b * b * b) :=
  trans (mul_right (trans (mul_right h a) (mul_left h b)) a) (mul_left h (b * b))

/-- `χ_ω` for a unit is a literal `μ₃` element (`Omega·Omega` rewritten to `Omega2`). -/
private theorem chiOmega_mu3 (p m x q : Nat) (hq1 : 0 < q) (hqlt : q < p) :
    chiOmega p m x q = ofInt 1 ∨ chiOmega p m x q = Omega ∨ chiOmega p m x q = Omega2 := by
  rcases chiOmega_unit_value p m x q hq1 hqlt with h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr (by rw [h]; decide))

/-- ★★★★★ **The cubic reciprocity law.**  `χ(q)` is the cubic residue symbol `(π/q)₃`: it lies in `μ₃`,
    is `≡ J^{(q²−1)/3} (mod q)`, and is the *unique* such `μ₃` value.  ∅-axiom (PURE). -/
theorem cubic_reciprocity_law {d : ZOmega} {p m x q s : Nat} (hp : 1 < p) (hp3 : 3 < p)
    (hpr : ∀ e, e ∣ p → e = 1 ∨ e = p) (h3m : 3 * m = p - 1) (hm1 : 1 ≤ m)
    (hdn : d.normSq = (p : Int)) (hω : ModEq d Omega (ofInt ((x : Nat) : Int)))
    (hx : p ∣ (x * x + x + 1)) (hq3 : q % 3 = 2) (hqr : ∀ e, e ∣ q → e = 1 ∨ e = q)
    (hcop : gcd213 q p = 1) (hq1 : 0 < q) (hqlt : q < p) (hs : q + 1 = 3 * (s + 1)) :
    -- (1) χ(q) is a cube root of unity
    (chiOmega p m x q = ofInt 1 ∨ chiOmega p m x q = Omega ∨ chiOmega p m x q = Omega2)
    -- (2) the reciprocity congruence `J^{(q²−1)/3} ≡ χ(q) (mod q)`
    ∧ ModEq (ofInt ((q : Nat) : Int)) (pow (jacobiSum p m x) ((2 * s + 1) + q * s)) (chiOmega p m x q)
    -- (3) well-definedness: χ(q) is the unique μ₃ value `J^{(q²−1)/3}` is congruent to
    ∧ (∀ V : ZOmega, (V = ofInt 1 ∨ V = Omega ∨ V = Omega2) →
        ModEq (ofInt ((q : Nat) : Int)) (pow (jacobiSum p m x) ((2 * s + 1) + q * s)) V →
        V = chiOmega p m x q) := by
  have hq1' : 1 < q := Nat.lt_of_lt_of_le (by decide) (hq3 ▸ Nat.mod_le q 3)
  have hcong := cubic_reciprocity_power_congr hp hp3 hpr h3m hm1 hdn hω hx hq3 hqr hcop hq1 hqlt hs
  have hχmu3 := chiOmega_mu3 p m x q hq1 hqlt
  refine ⟨hχmu3, hcong, ?_⟩
  intro V hVmu3 hJV
  exact mu3_eq_of_modEq hq1' hVmu3 hχmu3 (trans (symm hJV) hcong)

/-- ★★★★ **Existence of the residue symbol** — `J^{(q²−1)/3}` lands in `μ₃` mod `q`.  Its cube is
    `J^{q²−1} ≡ χ(q)³ = 1 (mod q)` (the congruence cubed), so `inert_cube_one_value` places it among
    `{1, ω, ω²}`.  With `cubic_reciprocity_law` (3) the value is pinned to `χ(q)`.  ∅-axiom (PURE). -/
theorem residue_symbol_exists {d : ZOmega} {p m x q s : Nat} (hp : 1 < p) (hp3 : 3 < p)
    (hpr : ∀ e, e ∣ p → e = 1 ∨ e = p) (h3m : 3 * m = p - 1) (hm1 : 1 ≤ m)
    (hdn : d.normSq = (p : Int)) (hω : ModEq d Omega (ofInt ((x : Nat) : Int)))
    (hx : p ∣ (x * x + x + 1)) (hq3 : q % 3 = 2) (hqr : ∀ e, e ∣ q → e = 1 ∨ e = q)
    (hcop : gcd213 q p = 1) (hq1 : 0 < q) (hqlt : q < p) (hs : q + 1 = 3 * (s + 1)) :
    ModEq (ofInt ((q : Nat) : Int)) (pow (jacobiSum p m x) ((2 * s + 1) + q * s)) (ofInt 1)
      ∨ ModEq (ofInt ((q : Nat) : Int)) (pow (jacobiSum p m x) ((2 * s + 1) + q * s)) Omega
      ∨ ModEq (ofInt ((q : Nat) : Int)) (pow (jacobiSum p m x) ((2 * s + 1) + q * s)) Omega2 := by
  have hq1' : 1 < q := Nat.lt_of_lt_of_le (by decide) (hq3 ▸ Nat.mod_le q 3)
  have hcong := cubic_reciprocity_power_congr hp hp3 hpr h3m hm1 hdn hω hx hq3 hqr hcop hq1 hqlt hs
  have hχcube : chiOmega p m x q * chiOmega p m x q * chiOmega p m x q = ofInt 1 := by
    rcases chiOmega_unit_value p m x q hq1 hqlt with h | h | h <;> rw [h] <;> decide
  have hcube : ModEq (ofInt ((q : Nat) : Int))
      (pow (jacobiSum p m x) ((2 * s + 1) + q * s) * pow (jacobiSum p m x) ((2 * s + 1) + q * s)
        * pow (jacobiSum p m x) ((2 * s + 1) + q * s)) (ofInt 1) := by
    have h3 := modEq_cube hcong
    rwa [hχcube] at h3
  exact inert_cube_one_value hq3 hqr hq1' hcube

/-- ★★★★★ **The cubic residue symbol `(π/q)₃` is well defined and equals `χ(q)`** — there is a *unique*
    `μ₃` value congruent to `J^{(q²−1)/3}` mod `q`, and it is `χ(q)`.  Existence among `{1,ω,ω²}` is
    `residue_symbol_exists`; `χ(q)` is one such value (`cubic_reciprocity_law` 1+2); uniqueness is (3).
    This is the cleanest statement of the symbol identity `(π/q)₃ = χ(q) = (q/π)₃`.  ∅-axiom (PURE). -/
theorem cubic_residue_symbol_well_defined {d : ZOmega} {p m x q s : Nat} (hp : 1 < p) (hp3 : 3 < p)
    (hpr : ∀ e, e ∣ p → e = 1 ∨ e = p) (h3m : 3 * m = p - 1) (hm1 : 1 ≤ m)
    (hdn : d.normSq = (p : Int)) (hω : ModEq d Omega (ofInt ((x : Nat) : Int)))
    (hx : p ∣ (x * x + x + 1)) (hq3 : q % 3 = 2) (hqr : ∀ e, e ∣ q → e = 1 ∨ e = q)
    (hcop : gcd213 q p = 1) (hq1 : 0 < q) (hqlt : q < p) (hs : q + 1 = 3 * (s + 1)) :
    ∃ V : ZOmega, ((V = ofInt 1 ∨ V = Omega ∨ V = Omega2)
        ∧ ModEq (ofInt ((q : Nat) : Int)) (pow (jacobiSum p m x) ((2 * s + 1) + q * s)) V)
      ∧ (∀ W : ZOmega, ((W = ofInt 1 ∨ W = Omega ∨ W = Omega2)
          ∧ ModEq (ofInt ((q : Nat) : Int)) (pow (jacobiSum p m x) ((2 * s + 1) + q * s)) W) →
            W = V) := by
  obtain ⟨hχmu3, hcong, huniq⟩ :=
    cubic_reciprocity_law hp hp3 hpr h3m hm1 hdn hω hx hq3 hqr hcop hq1 hqlt hs
  exact ⟨chiOmega p m x q, ⟨hχmu3, hcong⟩, fun W hW => huniq W hW.1 hW.2⟩

end E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicReciprocity
