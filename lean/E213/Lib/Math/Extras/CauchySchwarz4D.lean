import E213.Lib.Math.Extras.CauchySchwarz2D
import E213.Lib.Math.Extras.CauchySchwarz3D

/-!
# n = 4 Σ-Cauchy-Schwarz cross-term aggregator (∅-axiom)

Continuation of `CauchySchwarz3D`.  At n=4 there are
`C(4,2) = 6` cross-term pairs: (1,2), (1,3), (1,4), (2,3),
(2,4), (3,4).  Each contributes the n=2 cross-term inequality.

Pattern: for n=k there are `C(k,2)` pairs.  This file completes
n=4 explicitly; the general inductive step adding `(n-1)` new
pairs per level is captured by `CauchySchwarzInductive`.
-/

namespace E213.Lib.Math.Extras.CauchySchwarz4D

open E213.Lib.Math.Extras.CauchySchwarz2D (cross_term_le)

/-- ★ **4D cross-term aggregate** — 6 pair applications of the
    n=2 cross-term inequality.  -/
theorem cs_4d_cross_aggregate (a1 a2 a3 a4 b1 b2 b3 b4 : Nat) :
    2 * ((a1 * b1) * (a2 * b2)) + 2 * ((a1 * b1) * (a3 * b3))
    + 2 * ((a1 * b1) * (a4 * b4)) + 2 * ((a2 * b2) * (a3 * b3))
    + 2 * ((a2 * b2) * (a4 * b4)) + 2 * ((a3 * b3) * (a4 * b4))
    ≤ (a1*a1*(b2*b2) + a2*a2*(b1*b1))
      + (a1*a1*(b3*b3) + a3*a3*(b1*b1))
      + (a1*a1*(b4*b4) + a4*a4*(b1*b1))
      + (a2*a2*(b3*b3) + a3*a3*(b2*b2))
      + (a2*a2*(b4*b4) + a4*a4*(b2*b2))
      + (a3*a3*(b4*b4) + a4*a4*(b3*b3)) := by
  have h12 := cross_term_le a1 a2 b1 b2
  have h13 := cross_term_le a1 a3 b1 b3
  have h14 := cross_term_le a1 a4 b1 b4
  have h23 := cross_term_le a2 a3 b2 b3
  have h24 := cross_term_le a2 a4 b2 b4
  have h34 := cross_term_le a3 a4 b3 b4
  exact Nat.add_le_add
    (Nat.add_le_add
      (Nat.add_le_add
        (Nat.add_le_add (Nat.add_le_add h12 h13) h14) h23) h24) h34

end E213.Lib.Math.Extras.CauchySchwarz4D
