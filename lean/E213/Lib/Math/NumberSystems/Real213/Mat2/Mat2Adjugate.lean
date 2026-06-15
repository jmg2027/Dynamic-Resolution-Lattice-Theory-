import E213.Lib.Math.NumberSystems.Real213.ContinuedFraction.ContinuantDeterminant
import E213.Meta.Int213.PolyIntMTactic
import E213.Meta.Int213.Order

/-!
# Cyclic trace + adjugate / inverse for the integer 2×2 matrix (∅-axiom)

The foundational 2×2 linear-algebra facts behind Cramer's rule and the inverse
formula, on the corpus `Mat2` (`ModularElliptic`) with `detM` reused from
`ContinuantDeterminant`:

  * (T1) **cyclic trace** `tr(AB) = tr(BA)` (`traceM_mul_comm`);
  * (T2) **adjugate-inverse** `M · adj M = det(M)·I = adj M · M`, entrywise
    (`mat2_mul_adj`, `mat2_adj_mul`);
  * (T3) **det of adjugate** `det(adj M) = det M` (the 2×2 special case of
    `det(adj M) = (det M)^{n−1}`) (`detM_adj`);
  * `tr(I) = 2` (`traceM_I2`; `det(I)=1` is already `ContinuantDeterminant.detM_I2`).

All genuinely absent (no `tr_mul`, no matrix `adj`, no adjugate-inverse existed).
Diagonal/`det` entries close by `ring_intZ`; the off-diagonal `= 0` entries via a
`t − t` cancellation + `Order.sub_self_zero` (`ring_intZ`'s normaliser does not
reduce a cancellation to the literal `0`).  All ∅-axiom.
-/

namespace E213.Lib.Math.NumberSystems.Real213.Mat2.Mat2Adjugate

open E213.Lib.Math.NumberSystems.Real213.ModularGeometry.ModularElliptic (Mat2 mul I2)
open E213.Lib.Math.NumberSystems.Real213.ContinuedFraction.ContinuantDeterminant (detM)

/-- Trace `a + d`. -/
def traceM (M : Mat2) : Int := M.a + M.d

/-- Classical adjugate (adjoint) `[[d,−b],[−c,a]]`. -/
def adj (M : Mat2) : Mat2 := ⟨M.d, -M.b, -M.c, M.a⟩

/-- ★ **Cyclic trace.**  `tr(AB) = tr(BA)`. -/
theorem traceM_mul_comm (A B : Mat2) : traceM (mul A B) = traceM (mul B A) := by
  show (A.a * B.a + A.b * B.c) + (A.c * B.b + A.d * B.d)
     = (B.a * A.a + B.b * A.c) + (B.c * A.b + B.d * A.d)
  ring_intZ

/-- ★★ **Adjugate-inverse (right).**  `M · adj M = det(M)·I`, entrywise:
    diagonal entries `det M`, off-diagonal `0`. -/
theorem mat2_mul_adj (M : Mat2) :
    (mul M (adj M)).a = detM M
    ∧ (mul M (adj M)).b = 0
    ∧ (mul M (adj M)).c = 0
    ∧ (mul M (adj M)).d = detM M := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · show M.a * M.d + M.b * (-M.c) = M.a * M.d - M.b * M.c
    ring_intZ
  · show M.a * (-M.b) + M.b * M.a = 0
    calc M.a * (-M.b) + M.b * M.a
        = M.b * M.a - M.b * M.a := by ring_intZ
      _ = 0 := E213.Meta.Int213.Order.sub_self_zero _
  · show M.c * M.d + M.d * (-M.c) = 0
    calc M.c * M.d + M.d * (-M.c)
        = M.c * M.d - M.c * M.d := by ring_intZ
      _ = 0 := E213.Meta.Int213.Order.sub_self_zero _
  · show M.c * (-M.b) + M.d * M.a = M.a * M.d - M.b * M.c
    ring_intZ

/-- ★★ **Adjugate-inverse (left).**  `adj M · M = det(M)·I`, entrywise. -/
theorem mat2_adj_mul (M : Mat2) :
    (mul (adj M) M).a = detM M
    ∧ (mul (adj M) M).b = 0
    ∧ (mul (adj M) M).c = 0
    ∧ (mul (adj M) M).d = detM M := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · show M.d * M.a + (-M.b) * M.c = M.a * M.d - M.b * M.c
    ring_intZ
  · show M.d * M.b + (-M.b) * M.d = 0
    calc M.d * M.b + (-M.b) * M.d
        = M.b * M.d - M.b * M.d := by ring_intZ
      _ = 0 := E213.Meta.Int213.Order.sub_self_zero _
  · show (-M.c) * M.a + M.a * M.c = 0
    calc (-M.c) * M.a + M.a * M.c
        = M.a * M.c - M.a * M.c := by ring_intZ
      _ = 0 := E213.Meta.Int213.Order.sub_self_zero _
  · show (-M.c) * M.b + M.a * M.d = M.a * M.d - M.b * M.c
    ring_intZ

/-- ★ **Determinant of the adjugate.**  In the 2×2 case `det(adj M) = det M`
    (general `n×n`: `det(adj M) = (det M)^{n−1}`, here `n−1 = 1`). -/
theorem detM_adj (M : Mat2) : detM (adj M) = detM M := by
  show M.d * M.a - (-M.b) * (-M.c) = M.a * M.d - M.b * M.c
  ring_intZ

/-- `tr(I) = 2`. -/
theorem traceM_I2 : traceM I2 = 2 := by decide

end E213.Lib.Math.NumberSystems.Real213.Mat2.Mat2Adjugate
