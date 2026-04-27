import E213.Research.Real213CauchyArithSum
import E213.Research.Real213CauchyArithMul
import E213.Research.Real213CutSumOne
import E213.Research.Real213CutMulOne

/-!
# Research.Real213CauchyConstLimit: closed forms for arithmetic on
  constant Cauchy sequences.

For two CauchyCutSeqs each constant at a const cut (constCauchyCutSeq
of a constCut), the limit of their sum/mul equals the corresponding
const-cut closed form.
-/

namespace E213.Research.Real213CutSum

open E213.Firmware E213.Hypervisor

/-- Limit of (constCauchy a/1) + (constCauchy b/1) = (a+b)/1. -/
theorem constCauchy_cutSum_int (a b : Nat) :
    ((constCauchyCutSeq (constCut a 1)).cutSum
      (constCauchyCutSeq (constCut b 1))).limit
    = constCut (a+b) 1 := by
  rw [CauchyCutSeq.cutSum_limit, constCauchyCutSeq_limit]
  exact cutSum_int_int a b

/-- Limit of (constCauchy a/2) + (constCauchy b/2) = (a+b)/2. -/
theorem constCauchy_cutSum_half (a b : Nat) :
    ((constCauchyCutSeq (constCut a 2)).cutSum
      (constCauchyCutSeq (constCut b 2))).limit
    = constCut (a+b) 2 := by
  rw [CauchyCutSeq.cutSum_limit, constCauchyCutSeq_limit]
  exact cutSum_half_general a b

/-- Limit of (constCauchy 1) * (constCauchy 1) = 1. -/
theorem constCauchy_cutMul_one_one :
    ((constCauchyCutSeq (constCut 1 1)).cutMul
      (constCauchyCutSeq (constCut 1 1))).limit
    = constCut 1 1 := by
  rw [CauchyCutSeq.cutMul_limit, constCauchyCutSeq_limit]
  exact cutMul_one_one

end E213.Research.Real213CutSum
