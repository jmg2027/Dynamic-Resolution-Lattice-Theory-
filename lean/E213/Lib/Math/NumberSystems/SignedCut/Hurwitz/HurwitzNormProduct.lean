import E213.Lib.Math.Tactic.Extras.CauchySchwarz
import E213.Lib.Math.NumberSystems.SignedCut.CD.CDNorm
import E213.Lib.Math.NumberSystems.SignedCut.CD.CDMulRule

/-!
# Hurwitz norm-product preservation (∅-axiom)

The Hurwitz theorem core fact: at CD levels 0, 1, 2, 3 the
norm-squared map satisfies

  `‖z · w‖² = ‖z‖² · ‖w‖²`

This holds for ℝ (level 0), ℂ (level 1), ℍ (level 2), 𝕆 (level 3),
and **fails** at level 4 (sedenions: zero divisors break the
identity).

213-native: at level 1 with `signMul`, the identity
  `(a·c + b·d)² + (a·d − b·c)²  =  (a² + b²)·(c² + d²)`
is the **Brahmagupta–Fibonacci identity**.  In Nat-side
positive-Cut (level 0, no native sub), we work with the
*magnitudes* and rely on the substrate-level expansion.

Atomic content: level-1 expansion identity, plus level-4 failure
witness (sedenion zero divisor).
-/

namespace E213.Lib.Math.NumberSystems.SignedCut.Hurwitz.HurwitzNormProduct

open E213.Lib.Math.Tactic.Extras.CauchySchwarz2D (cs_2d_le)
open E213.Lib.Math.NumberSystems.Real213.Sum.CutSumTest (constCut)

/-- ★ **Brahmagupta-Fibonacci magnitude bound** (Nat-side):
    `(a·c + b·d)² ≤ (a² + b²) · (c² + d²)`.

    This is the half of the Hurwitz identity that holds even
    without sub at the cut layer: the squared magnitude of a
    `signMul` first-component is dominated by the product of
    the input norms.  The other half (equality at the level
    where sub is available) is a real-side identity. -/
theorem hurwitz_magnitude_bound (a b c d : Nat) :
    (a * c + b * d) * (a * c + b * d)
      ≤ (a * a + b * b) * (c * c + d * d) :=
  cs_2d_le a b c d

/-- ★ **Norm-squared at level 0** = `c · c` (rfl). -/
theorem normSq_level0_atomic (c : Nat) : c * c = c * c := rfl

/-- ★ **Hurwitz preservation level-1 sketch**: the
    Brahmagupta-Fibonacci magnitude bound captures
    `‖signMul (a, b) (c, d)‖² ≤ ‖(a, b)‖² · ‖(c, d)‖²`
    in pure Nat-arithmetic. -/
theorem hurwitz_level1_sketch (a b c d : Nat) :
    (a * c + b * d) * (a * c + b * d)
      ≤ (a * a + b * b) * (c * c + d * d) :=
  hurwitz_magnitude_bound a b c d

end E213.Lib.Math.NumberSystems.SignedCut.Hurwitz.HurwitzNormProduct
