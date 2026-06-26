import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCharSumZero
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinJacobiNorm

/-!
# `χ²`-orthogonality — `Σ_{i∈tot} χ_ω(i)² = 0` (∅-axiom)

For a cubic character, the square equals the conjugate (`χ(t)² = conj χ(t)`, since each value lies in
`{0,1,ω,ω²}` and `conj` is the `μ₃`-inverse, `conj_chiOmega_eq_sq`).  Hence the `χ²`-orthogonality
follows from the `χ`-orthogonality by conjugation:

  `Σ_{i∈tot} χ_ω(i)² = Σ_{i∈tot} conj χ_ω(i) = conj (Σ_{i∈tot} χ_ω(i)) = conj 0 = 0`  (`chiOmega_sq_orth`).

This is the orthogonality behind the `n=0` Gauss-square coefficient `(g⋆g)(0)=0`, the last coefficient
of `g(χ)² = J·g(χ²)`.  ∅-axiom.
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicCharSq

open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega (ZOmega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega.ZOmega (ofInt Omega conj)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicCharFp (chiOmega chiOmega_value)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCongruence (ModEq)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCharSumZero (chiListSum chiListSum_totatives_zero)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinJacobiNorm (conj_listSum conj_zero)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinListSum (listSum listSum_congr)
open E213.Lib.Math.NumberTheory.EulerTheorem (totativeList)

/-- ★★★ **`conj χ_ω(t) = χ_ω(t)²`** — the conjugate of a cubic-character value is its square (`μ₃`:
    `conj z = z⁻¹ = z²` for `z³=1`).  By cases on the four possible values.  ∅-axiom. -/
theorem conj_chiOmega_eq_sq (p m x t : Nat) :
    conj (chiOmega p m x t) = chiOmega p m x t * chiOmega p m x t := by
  rcases chiOmega_value p m x t with h | h | h | h <;> rw [h] <;> decide

/-- `listSum (chiOmega p m x) L = chiListSum p m x L`. -/
private theorem listSum_chiOmega (p m x : Nat) :
    ∀ L : List Nat, listSum (chiOmega p m x) L = chiListSum p m x L
  | [] => rfl
  | t :: l => by
      show chiOmega p m x t + listSum (chiOmega p m x) l = chiOmega p m x t + chiListSum p m x l
      rw [listSum_chiOmega p m x l]

/-- ★★★★ **`χ²`-orthogonality** — `Σ_{i∈tot} χ_ω(i)² = 0` for a prime `p ≡ 1 mod 3` (`p>3`).  Each
    term is `conj χ_ω(i)`; the sum is `conj (Σ χ_ω(i)) = conj 0 = 0` (`chiListSum_totatives_zero`).
    ∅-axiom. -/
theorem chiOmega_sq_orth {d : ZOmega} {p m x : Nat} (hp : 1 < p) (hp3 : 3 < p)
    (hpr : ∀ k, k ∣ p → k = 1 ∨ k = p) (h3m : 3 * m = p - 1) (hm1 : 1 ≤ m)
    (hdn : d.normSq = (p : Int)) (hω : ModEq d Omega (ofInt ((x : Nat) : Int)))
    (hx : p ∣ (x * x + x + 1)) :
    listSum (fun i => chiOmega p m x i * chiOmega p m x i) (totativeList p) = 0 := by
  rw [listSum_congr (totativeList p) (fun i _ => (conj_chiOmega_eq_sq p m x i).symm),
      ← conj_listSum (chiOmega p m x) (totativeList p), listSum_chiOmega p m x,
      chiListSum_totatives_zero hp hp3 hpr h3m hm1 hdn hω hx, conj_zero]

end E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinCubicCharSq
