import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicCharValue
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinDvd
import E213.Lib.Math.NumberTheory.PolyRoot.IntEuclid
import E213.Meta.Tactic.Pow213

/-!
# The cubic character value is well-defined in `μ₃` (∅-axiom)

★★★★ `root_unique` : for a norm-`p` Eisenstein prime `d` with `p > 3`, the three cube roots of unity
`{1, ω, ω²}` are **pairwise distinct mod `d`**.  Hence the cubic-character value of `cube_one_value`
(some `u ∈ {1,ω,ω²}` with `χ(α) ≡ u`) is **unique** — the character `(·/d)₃` is a well-defined
`μ₃`-valued *function*, not merely a relation.

The mechanism: any two distinct roots differ by an element of **norm 3** (`1−ω, 1−ω², ω−ω²` all have
norm 3); if `d ∣ (u − v)` then `p = ‖d‖² ∣ ‖u−v‖² = 3`, forcing `p ≤ 3` — impossible for `p > 3`.
Well-definedness in `μ₃` is the prerequisite for the cubic character as a function on `𝔽_p` (toward the
Jacobi sum `J(χ,χ)`).  ∅-axiom.
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicCharWelldef

open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega (ZOmega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega.ZOmega
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCongruence (ModEq trans symm)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.RootOfUnityOrthogonality (pow)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinDvd (normSq_dvd_of_dvd)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicCharValue (cube_one_value)
open E213.Lib.Math.NumberTheory.PolyRoot (int_dvd_to_nat)
open E213.Tactic.Pow213 (le_of_dvd_pos)

/-- ★★★★ **The three cube roots of unity are distinct mod a norm-`p` prime (`p > 3`).**  If `u ≡ v
    (mod d)` for `u, v ∈ {1, ω, ω²}`, then `u = v`.  Distinct roots differ by a norm-3 element, and
    `‖d‖² = p ∤ 3` for `p > 3`.  ∅-axiom. -/
theorem root_unique {d : ZOmega} {p : Nat} (hp3 : 3 < p) (hdp : d.normSq = (p : Int))
    {u v : ZOmega} (hu : u = ofInt 1 ∨ u = Omega ∨ u = Omega2)
    (hv : v = ofInt 1 ∨ v = Omega ∨ v = Omega2) (h : ModEq d u v) : u = v := by
  rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl <;>
    first
      | rfl
      | (exfalso
         obtain ⟨c, hc⟩ := h
         have hd3 : d.normSq ∣ (3 : Int) := normSq_dvd_of_dvd d _ c hc
         rw [hdp] at hd3
         have hnat : p ∣ 3 := int_dvd_to_nat p 3 hd3
         exact absurd (le_of_dvd_pos p 3 (by decide) hnat) (Nat.not_le.mpr hp3))

/-- ★★★★★ **The cubic character is a well-defined `μ₃`-valued function.**  For a norm-`p` prime `d`
    (`p > 3`), the character value `y` (`= α^m`, with `y³ ≡ 1`) is congruent to a **unique** element of
    `{1, ω, ω²}` mod `d`.  Existence from `cube_one_value`, uniqueness from `root_unique`.  ∅-axiom. -/
theorem char_value_unique {d y : ZOmega} {p : Nat}
    (hpr : ∀ e, e ∣ p → e = 1 ∨ e = p) (hp1 : 1 < p) (hp3 : 3 < p) (hd : d.normSq = (p : Int))
    (hcube : ModEq d (y * y * y) (ofInt 1)) :
    ∃ u, (u = ofInt 1 ∨ u = Omega ∨ u = Omega2) ∧ ModEq d y u ∧
      (∀ w, (w = ofInt 1 ∨ w = Omega ∨ w = Omega2) → ModEq d y w → w = u) := by
  rcases cube_one_value hpr hp1 hd hcube with h1 | hω | hω2
  · exact ⟨ofInt 1, Or.inl rfl, h1,
      fun w hw hw' => root_unique hp3 hd hw (Or.inl rfl) (trans (symm hw') h1)⟩
  · exact ⟨Omega, Or.inr (Or.inl rfl), hω,
      fun w hw hw' => root_unique hp3 hd hw (Or.inr (Or.inl rfl)) (trans (symm hw') hω)⟩
  · exact ⟨Omega2, Or.inr (Or.inr rfl), hω2,
      fun w hw hw' => root_unique hp3 hd hw (Or.inr (Or.inr rfl)) (trans (symm hw') hω2)⟩

end E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicCharWelldef
