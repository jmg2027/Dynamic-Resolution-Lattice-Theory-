import E213.Meta.Int213.PolyIntMTactic

/-!
# Pell / ℤ[√2]-norm multiplicative closure (∅-axiom)

Existential closures of the two `D = 2` real-quadratic norm forms (mirroring the
sum-of-two-squares and Eisenstein-form closures):

  * `a² + 2b²` — the ℤ[√−2] norm (`isNorm2_mul`, witnesses `(ac−2bd, ad+bc)`).
  * `a² − 2b²` — the genuine **Pell norm** ℤ[√2], indefinite (`isPell_mul`,
    witnesses `(ac+2bd, ad+bc)` — the Brahmagupta D=2 identity
    `(a²−2b²)(c²−2d²) = (ac+2bd)² − 2(ad+bc)²`).
  * ★ `pell_one_compose` — the **Pell-solution group law**: solutions of `x²−2y²=1`
    compose via `(ac+2bd, ad+bc)`, the engine behind `(1+√2)ⁿ`.

Genuinely absent: only the *plus-D identity* `int_quad_diophantus_sqrt2` existed
(as a bare ring identity); the `a²−2b²` Pell form, both closures, and the group
law are new.  All ∅-axiom.
-/

namespace E213.Lib.Math.NumberTheory.PellNorm

open E213.Meta.Int213.PolyIntM

/-- `n` is of the form `a² + 2b²` (the ℤ[√−2] norm). -/
def isNorm2 (n : Int) : Prop := ∃ a b : Int, n = a*a + 2*(b*b)

theorem isNorm2_one : isNorm2 1 := ⟨1, 0, by decide⟩

/-- ★ **`a² + 2b²` closure.**  Witnesses `(ac − 2bd, ad + bc)`. -/
theorem isNorm2_mul {m n : Int}
    (hm : isNorm2 m) (hn : isNorm2 n) : isNorm2 (m * n) := by
  obtain ⟨a, b, hm⟩ := hm
  obtain ⟨c, d, hn⟩ := hn
  exact ⟨a*c - 2*(b*d), a*d + b*c, by rw [hm, hn]; ring_intZ⟩

/-- `n` is of the form `a² − 2b²` (the Pell / ℤ[√2] norm). -/
def isPell (n : Int) : Prop := ∃ a b : Int, n = a*a - 2*(b*b)

theorem isPell_one : isPell 1 := ⟨1, 0, by decide⟩

/-- `-1 = 1² − 2·1²`, the fundamental Pell unit norm `N(1+√2) = −1`. -/
theorem isPell_neg_one : isPell (-1) := ⟨1, 1, by decide⟩

/-- ★ **Pell `a² − 2b²` closure.**  Witnesses `(ac + 2bd, ad + bc)`; the identity
    `(a²−2b²)(c²−2d²) = (ac+2bd)² − 2(ad+bc)²` is the engine behind composition of
    Pell-equation solutions `(1+√2)ⁿ`. -/
theorem isPell_mul {m n : Int}
    (hm : isPell m) (hn : isPell n) : isPell (m * n) := by
  obtain ⟨a, b, hm⟩ := hm
  obtain ⟨c, d, hn⟩ := hn
  exact ⟨a*c + 2*(b*d), a*d + b*c, by rw [hm, hn]; ring_intZ⟩

/-- ★ **Pell solutions compose.**  If `(a,b)` and `(c,d)` solve `x²−2y²=1`, then
    `(ac+2bd, ad+bc)` does too — the group law on Pell solutions. -/
theorem pell_one_compose {a b c d : Int}
    (h1 : a*a - 2*(b*b) = 1) (h2 : c*c - 2*(d*d) = 1) :
    (a*c + 2*(b*d))*(a*c + 2*(b*d)) - 2*((a*d + b*c)*(a*d + b*c)) = 1 := by
  have key : (a*c + 2*(b*d))*(a*c + 2*(b*d)) - 2*((a*d + b*c)*(a*d + b*c))
           = (a*a - 2*(b*b)) * (c*c - 2*(d*d)) := by ring_intZ
  rw [key, h1, h2]; decide

end E213.Lib.Math.NumberTheory.PellNorm
