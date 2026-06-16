import E213.Meta.Int213.PolyIntMTactic

/-!
# `D = 5` quadratic-norm multiplicative closure — the golden field `ℚ(√5)` (∅-axiom)

The `D=5` companions of `PellNorm`/`Norm3`, for the field underlying the golden ratio and
Fibonacci/Lucas (`lucasZ_sq`: `L_m² − 5F_m² = ±4`):

  * `a² + 5b²` — the ℤ[√−5] norm (`isNorm5_mul`, `(ac − 5bd, ad + bc)`).
  * `a² − 5b²` — the indefinite ℤ[√5] norm (`isNorm5neg_mul`, `(ac + 5bd, ad + bc)`) + the
    Pell group law for `x² − 5y² = 1` (fundamental solution `(9,4)`, the engine of `(9+4√5)ⁿ`).

All ∅-axiom (Brahmagupta–Fibonacci `D=5` identities, `ring_intZ`).
-/

namespace E213.Lib.Math.NumberTheory.Norm5

open E213.Meta.Int213.PolyIntM

/-- `n` is of the form `a² + 5b²` (the ℤ[√−5] norm). -/
def isNorm5 (n : Int) : Prop := ∃ a b : Int, n = a*a + 5*(b*b)

theorem isNorm5_one : isNorm5 1 := ⟨1, 0, by decide⟩
theorem isNorm5_six : isNorm5 6 := ⟨1, 1, by decide⟩

/-- ★ **`a² + 5b²` closure.**  Witnesses `(ac − 5bd, ad + bc)`. -/
theorem isNorm5_mul {m n : Int}
    (hm : isNorm5 m) (hn : isNorm5 n) : isNorm5 (m * n) := by
  obtain ⟨a, b, hm⟩ := hm
  obtain ⟨c, d, hn⟩ := hn
  exact ⟨a*c - 5*(b*d), a*d + b*c, by rw [hm, hn]; ring_intZ⟩

/-- `n` is of the form `a² − 5b²` (the indefinite ℤ[√5] norm — the golden-field norm). -/
def isNorm5neg (n : Int) : Prop := ∃ a b : Int, n = a*a - 5*(b*b)

theorem isNorm5neg_one : isNorm5neg 1 := ⟨1, 0, by decide⟩
/-- `−4 = 1² − 5·1²`: the Lucas/Fibonacci Cassini value `L_m² − 5F_m² = ±4` realized. -/
theorem isNorm5neg_neg_four : isNorm5neg (-4) := ⟨1, 1, by decide⟩

/-- ★ **`a² − 5b²` closure.**  Witnesses `(ac + 5bd, ad + bc)`. -/
theorem isNorm5neg_mul {m n : Int}
    (hm : isNorm5neg m) (hn : isNorm5neg n) : isNorm5neg (m * n) := by
  obtain ⟨a, b, hm⟩ := hm
  obtain ⟨c, d, hn⟩ := hn
  exact ⟨a*c + 5*(b*d), a*d + b*c, by rw [hm, hn]; ring_intZ⟩

/-- ★ **Pell `x² − 5y² = 1` solutions compose** via `(ac + 5bd, ad + bc)` — the group law
    behind `(9 + 4√5)ⁿ` (fundamental solution `(9,4)`: `9² − 5·4² = 81 − 80 = 1`). -/
theorem pell5_one_compose {a b c d : Int}
    (h1 : a*a - 5*(b*b) = 1) (h2 : c*c - 5*(d*d) = 1) :
    (a*c + 5*(b*d))*(a*c + 5*(b*d)) - 5*((a*d + b*c)*(a*d + b*c)) = 1 := by
  have key : (a*c + 5*(b*d))*(a*c + 5*(b*d)) - 5*((a*d + b*c)*(a*d + b*c))
      = (a*a - 5*(b*b)) * (c*c - 5*(d*d)) := by ring_intZ
  rw [key, h1, h2]; decide

/-- The fundamental solution `(9,4)` of `x² − 5y² = 1`. -/
theorem pell5_fundamental : (9:Int)*9 - 5*(4*4) = 1 := by decide

end E213.Lib.Math.NumberTheory.Norm5
