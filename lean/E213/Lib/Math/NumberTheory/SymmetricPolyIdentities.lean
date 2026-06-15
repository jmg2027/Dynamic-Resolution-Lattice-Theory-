import E213.Meta.Int213.PolyIntMTactic

/-!
# Symmetric-polynomial identities: Vieta's formulas + Newton's identities (∅-axiom)

Two genuinely-absent classical families relating the **roots** of a polynomial to
its **coefficients** (the elementary symmetric functions `e₁,e₂,e₃`) and to the
**power sums** `p₁,p₂,p₃` — all one-line `ring_intZ` over `Int`.

## Vieta's formulas (roots ↔ coefficients)
  * `vieta2` : `(x−r)(x−s) = x² − (r+s)x + rs`.
  * `vieta3` : `(x−r)(x−s)(x−t) = x³ − (r+s+t)x² + (rs+st+tr)x − rst`.
  * `vieta_discriminant` : `(r−s)² = (r+s)² − 4rs`.

## Newton's identities (power sums ↔ elementary symmetric)
  * `p2_two`/`p2_three` : `p₂ = e₁² − 2e₂` (2- and 3-variable).
  * `newton_p3` : `p₃ = e₁p₂ − e₂p₁ + 3e₃` (the genuine Newton recurrence).
  * `e1_sq` : `e₁² = p₂ + 2e₂`; `e1_cube` : `e₁³ = p₃ + 3e₁e₂ − 3e₃`.

Genuinely absent (the `Newton`/`Vieta` corpus hits are physics/interpolation
docstrings; `Positivity.prod_sum_le_sq_sum` is the *inequality* version, and
`FactorIdentities.sum_cubes_three` a *factorization*).  All ∅-axiom.
-/

namespace E213.Lib.Math.NumberTheory.SymmetricPolyIdentities

open E213.Meta.Int213.PolyIntM

/-! ## Vieta's formulas -/

/-- **Quadratic Vieta**: a monic quadratic with roots `r,s` has `x`-coefficient
    `−(r+s)` and constant `r·s`. -/
theorem vieta2 (x r s : Int) :
    (x - r) * (x - s) = x*x - (r + s)*x + r*s := by ring_intZ

/-- **Cubic Vieta**: the monic cubic's coefficients are the signed elementary
    symmetric functions of the roots `r,s,t`. -/
theorem vieta3 (x r s t : Int) :
    (x - r) * (x - s) * (x - t)
      = x*x*x - (r + s + t)*(x*x) + (r*s + s*t + t*r)*x - r*s*t := by ring_intZ

/-- **Discriminant identity**: `(r−s)² = (r+s)² − 4rs` (root-gap from coefficients). -/
theorem vieta_discriminant (r s : Int) :
    (r - s) * (r - s) = (r + s) * (r + s) - 4*(r*s) := by ring_intZ

/-- Concrete smoke: `(x−2)(x−3) = x² − 5x + 6`. -/
theorem vieta_smoke (x : Int) : (x - 2) * (x - 3) = x*x - 5*x + 6 := by ring_intZ

/-! ## Newton's identities -/

/-- **2-variable** `p₂ = e₁² − 2e₂`. -/
theorem p2_two (a b : Int) :
    a*a + b*b = (a + b) * (a + b) - 2*(a*b) := by ring_intZ

/-- **3-variable** `p₂ = e₁² − 2e₂`. -/
theorem p2_three (a b c : Int) :
    a*a + b*b + c*c = (a + b + c) * (a + b + c) - 2*(a*b + b*c + c*a) := by ring_intZ

/-- ★ **Newton's identity** `p₃ = e₁·p₂ − e₂·p₁ + 3·e₃`. -/
theorem newton_p3 (a b c : Int) :
    a*a*a + b*b*b + c*c*c
      = (a + b + c) * (a*a + b*b + c*c)
        - (a*b + b*c + c*a) * (a + b + c)
        + 3*(a*b*c) := by ring_intZ

/-- `e₁² = p₂ + 2e₂`. -/
theorem e1_sq (a b c : Int) :
    (a + b + c) * (a + b + c) = a*a + b*b + c*c + 2*(a*b + b*c + c*a) := by ring_intZ

/-- `e₁³ = p₃ + 3·e₁·e₂ − 3·e₃`. -/
theorem e1_cube (a b c : Int) :
    (a + b + c) * (a + b + c) * (a + b + c)
      = a*a*a + b*b*b + c*c*c
        + 3*((a + b + c) * (a*b + b*c + c*a))
        - 3*(a*b*c) := by ring_intZ

end E213.Lib.Math.NumberTheory.SymmetricPolyIdentities
