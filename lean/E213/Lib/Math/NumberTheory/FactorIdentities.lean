import E213.Meta.Int213.PolyIntMTactic

/-!
# Sum/difference factorizations of squares & cubes (∅-axiom, over `Int`)

The classical low-degree factorizations and their divisibility corollaries,
genuinely absent (only `PythagoreanTriples.leg_factor` `m²−n²=(m−n)(m+n)` existed):

  * `diff_of_squares` : `a² − b² = (a+b)(a−b)`
  * `sum_of_cubes`     : `a³ + b³ = (a+b)(a²−ab+b²)`
  * `diff_of_cubes`    : `a³ − b³ = (a−b)(a²+ab+b²)`
  * divisibility corollaries `(a+b)∣(a³+b³)`, `(a−b)∣(a³−b³)`, `(a±b)∣(a²−b²)`
  * `sum_cubes_three`  : `a³+b³+c³−3abc = (a+b+c)(a²+b²+c²−ab−bc−ca)`

All identities are one-line `ring_intZ`; the `∣` corollaries are
`⟨cofactor, by ring_intZ⟩` (no `rw`/propext).  All ∅-axiom.
-/

namespace E213.Lib.Math.NumberTheory.FactorIdentities

open E213.Meta.Int213.PolyIntM

/-- **Difference of squares**: `a² − b² = (a+b)(a−b)`. -/
theorem diff_of_squares (a b : Int) : a*a - b*b = (a + b) * (a - b) := by ring_intZ

/-- **Sum of cubes**: `a³ + b³ = (a+b)(a²−ab+b²)`. -/
theorem sum_of_cubes (a b : Int) :
    a*a*a + b*b*b = (a + b) * (a*a - a*b + b*b) := by ring_intZ

/-- **Difference of cubes**: `a³ − b³ = (a−b)(a²+ab+b²)`. -/
theorem diff_of_cubes (a b : Int) :
    a*a*a - b*b*b = (a - b) * (a*a + a*b + b*b) := by ring_intZ

/-- `(a+b) ∣ (a³+b³)`. -/
theorem add_dvd_sum_cubes (a b : Int) : (a + b) ∣ (a*a*a + b*b*b) :=
  ⟨a*a - a*b + b*b, by ring_intZ⟩

/-- `(a−b) ∣ (a³−b³)`. -/
theorem sub_dvd_diff_cubes (a b : Int) : (a - b) ∣ (a*a*a - b*b*b) :=
  ⟨a*a + a*b + b*b, by ring_intZ⟩

/-- `(a+b) ∣ (a²−b²)`. -/
theorem add_dvd_diff_squares (a b : Int) : (a + b) ∣ (a*a - b*b) :=
  ⟨a - b, by ring_intZ⟩

/-- `(a−b) ∣ (a²−b²)`. -/
theorem sub_dvd_diff_squares (a b : Int) : (a - b) ∣ (a*a - b*b) :=
  ⟨a + b, by ring_intZ⟩

/-- ★ **Three-variable cubic factorization**:
    `a³+b³+c³−3abc = (a+b+c)(a²+b²+c²−ab−bc−ca)`. -/
theorem sum_cubes_three (a b c : Int) :
    a*a*a + b*b*b + c*c*c - 3*(a*b*c)
      = (a + b + c) * (a*a + b*b + c*c - a*b - b*c - c*a) := by ring_intZ

end E213.Lib.Math.NumberTheory.FactorIdentities
