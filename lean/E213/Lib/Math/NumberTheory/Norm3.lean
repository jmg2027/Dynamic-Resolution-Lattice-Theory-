import E213.Meta.Int213.PolyIntMTactic

/-!
# `D = 3` quadratic-norm multiplicative closure (∅-axiom)

Existential closures of the two `D = 3` real-quadratic norm forms (the `D=3` companions of
`PellNorm`'s `D=2` results):

  * `a² + 3b²` — the ℤ[√−3] / Eisenstein-adjacent norm (`isNorm3_mul`, witnesses
    `(ac − 3bd, ad + bc)`; Brahmagupta `(a²+3b²)(c²+3d²) = (ac−3bd)² + 3(ad+bc)²`).
  * `a² − 3b²` — the indefinite ℤ[√3] norm (`isNorm3neg_mul`, witnesses `(ac + 3bd, ad + bc)`;
    `(a²−3b²)(c²−3d²) = (ac+3bd)² − 3(ad+bc)²`) + the Pell group law for `x² − 3y² = 1`.

All ∅-axiom (the closures are the Brahmagupta–Fibonacci `D=3` identities, by `ring_intZ`).
-/

namespace E213.Lib.Math.NumberTheory.Norm3

open E213.Meta.Int213.PolyIntM

/-- `n` is of the form `a² + 3b²` (the ℤ[√−3] norm). -/
def isNorm3 (n : Int) : Prop := ∃ a b : Int, n = a*a + 3*(b*b)

theorem isNorm3_one : isNorm3 1 := ⟨1, 0, by decide⟩
theorem isNorm3_four : isNorm3 4 := ⟨1, 1, by decide⟩

/-- ★ **`a² + 3b²` closure.**  Witnesses `(ac − 3bd, ad + bc)`. -/
theorem isNorm3_mul {m n : Int}
    (hm : isNorm3 m) (hn : isNorm3 n) : isNorm3 (m * n) := by
  obtain ⟨a, b, hm⟩ := hm
  obtain ⟨c, d, hn⟩ := hn
  exact ⟨a*c - 3*(b*d), a*d + b*c, by rw [hm, hn]; ring_intZ⟩

/-- `n` is of the form `a² − 3b²` (the indefinite ℤ[√3] norm). -/
def isNorm3neg (n : Int) : Prop := ∃ a b : Int, n = a*a - 3*(b*b)

theorem isNorm3neg_one : isNorm3neg 1 := ⟨1, 0, by decide⟩
/-- `−2 = 1² − 3·1²`, the fundamental unit norm `N(1+√3)`. -/
theorem isNorm3neg_neg_two : isNorm3neg (-2) := ⟨1, 1, by decide⟩

/-- ★ **`a² − 3b²` closure.**  Witnesses `(ac + 3bd, ad + bc)`; the engine behind the
    Pell-equation `x² − 3y² = 1` solution composition `(2 + √3)ⁿ`. -/
theorem isNorm3neg_mul {m n : Int}
    (hm : isNorm3neg m) (hn : isNorm3neg n) : isNorm3neg (m * n) := by
  obtain ⟨a, b, hm⟩ := hm
  obtain ⟨c, d, hn⟩ := hn
  exact ⟨a*c + 3*(b*d), a*d + b*c, by rw [hm, hn]; ring_intZ⟩

/-- ★ **Pell `x² − 3y² = 1` solutions compose** via `(ac + 3bd, ad + bc)` — the group law
    behind `(2 + √3)ⁿ` (fundamental solution `(2,1)`: `2² − 3·1² = 1`). -/
theorem pell3_one_compose {a b c d : Int}
    (h1 : a*a - 3*(b*b) = 1) (h2 : c*c - 3*(d*d) = 1) :
    (a*c + 3*(b*d))*(a*c + 3*(b*d)) - 3*((a*d + b*c)*(a*d + b*c)) = 1 := by
  have key : (a*c + 3*(b*d))*(a*c + 3*(b*d)) - 3*((a*d + b*c)*(a*d + b*c))
      = (a*a - 3*(b*b)) * (c*c - 3*(d*d)) := by ring_intZ
  rw [key, h1, h2]
  decide

/-- The fundamental solution `(2,1)` of `x² − 3y² = 1`. -/
theorem pell3_fundamental : (2:Int)*2 - 3*(1*1) = 1 := by decide

end E213.Lib.Math.NumberTheory.Norm3
