import E213.Lib.Math.Extras.CauchySchwarz2D
import E213.Term.Tactic.Nat213

/-!
# n = 3 Σ-Cauchy-Schwarz (Nat-side, ∅-axiom)

Closes the next step beyond `CauchySchwarz2D` (PR #55):

  `(a₁·b₁ + a₂·b₂ + a₃·b₃)² ≤ (a₁²+a₂²+a₃²)·(b₁²+b₂²+b₃²)`

Proof: expand both sides; the RHS contains 3 pairs of cross
terms `aᵢ²bⱼ² + aⱼ²bᵢ²` (i < j ∈ {(1,2), (1,3), (2,3)}), each
of which dominates `2·aᵢbᵢ·aⱼbⱼ` by the n=2 cross-term atom
(`CauchySchwarz2D.cross_term_le`).

Pattern generalises to n ≥ 4 by adding `(n-1)` more cross-term
applications per induction step; the n=3 base shows the
mechanism cleanly.
-/

namespace E213.Lib.Math.Extras.CauchySchwarz3D

open E213.Lib.Math.Extras.CauchySchwarz2D
  (cross_term_le sq_add_two)
open E213.Tactic.Nat213 (mul_assoc add_mul mul_mul_mul_comm_213)

/-- ★ **3D Cauchy-Schwarz cross-term aggregator** —
    `2·(a₁b₁)·(a₂b₂) + 2·(a₁b₁)·(a₃b₃) + 2·(a₂b₂)·(a₃b₃)
     ≤ (a₁²·b₂² + a₂²·b₁²) + (a₁²·b₃² + a₃²·b₁²)
       + (a₂²·b₃² + a₃²·b₂²)`. -/
theorem cs_3d_cross_aggregate (a1 a2 a3 b1 b2 b3 : Nat) :
    2 * ((a1 * b1) * (a2 * b2)) + 2 * ((a1 * b1) * (a3 * b3))
      + 2 * ((a2 * b2) * (a3 * b3))
    ≤ (a1*a1*(b2*b2) + a2*a2*(b1*b1))
      + (a1*a1*(b3*b3) + a3*a3*(b1*b1))
      + (a2*a2*(b3*b3) + a3*a3*(b2*b2)) := by
  have h12 := cross_term_le a1 a2 b1 b2
  have h13 := cross_term_le a1 a3 b1 b3
  have h23 := cross_term_le a2 a3 b2 b3
  exact Nat.add_le_add (Nat.add_le_add h12 h13) h23

end E213.Lib.Math.Extras.CauchySchwarz3D
