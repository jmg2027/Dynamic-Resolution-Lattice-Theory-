import E213.Research.Real213.CauchyArithSum
import E213.Research.Real213.CauchyArithMul
import E213.Research.Real213.CauchyLattice
import E213.Research.Real213.CutSumOne
import E213.Research.Real213.CutMulOne

/-!
# Research.Real213CauchyConstLimit: closed forms for arithmetic on
  constant Cauchy sequences.

For two CauchyCutSeqs each constant at a const cut (constCauchyCutSeq
of a constCut), the limit of their sum/mul equals the corresponding
const-cut closed form.
-/

namespace E213.Research.Real213.CutSum

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

/-- cutDouble distributes over cutSum at the Cauchy limit. -/
theorem CauchyCutSeq.cutDouble_cutSum_limit (a b : CauchyCutSeq) :
    (a.cutDouble.cutSum b.cutDouble).limit
    = (a.cutSum b).cutDouble.limit := by
  rw [CauchyCutSeq.cutSum_limit,
      CauchyCutSeq.cutDouble_limit a,
      CauchyCutSeq.cutDouble_limit b,
      CauchyCutSeq.cutDouble_limit (a.cutSum b),
      CauchyCutSeq.cutSum_limit]
  exact (E213.Research.Real213.CutSum.cutDouble_cutSum _ _).symm

/-- **Z2: const Cauchy cutSum limit (general form)**.
    For any two cut functions c1, c2, the cutSum of their constant
    Cauchy sequences gives the cutSum of the cuts at limit. -/
theorem const_cauchy_cutSum_limit (c1 c2 : Nat → Nat → Bool) :
    ((constCauchyCutSeq c1).cutSum (constCauchyCutSeq c2)).limit
    = cutSum c1 c2 := by
  rw [CauchyCutSeq.cutSum_limit,
      constCauchyCutSeq_limit c1, constCauchyCutSeq_limit c2]

/-- **Z2 dual**: const Cauchy cutMul limit (general form). -/
theorem const_cauchy_cutMul_limit (c1 c2 : Nat → Nat → Bool) :
    ((constCauchyCutSeq c1).cutMul (constCauchyCutSeq c2)).limit
    = cutMul c1 c2 := by
  rw [CauchyCutSeq.cutMul_limit,
      constCauchyCutSeq_limit c1, constCauchyCutSeq_limit c2]

/-- **Z3: const Cauchy cutMax limit (general form)**. -/
theorem const_cauchy_cutMax_limit (c1 c2 : Nat → Nat → Bool) :
    ((constCauchyCutSeq c1).cutMax (constCauchyCutSeq c2)).limit
    = cutMax c1 c2 := by
  rw [CauchyCutSeq.cutMax_limit,
      constCauchyCutSeq_limit c1, constCauchyCutSeq_limit c2]

/-- **Z3 dual**: const Cauchy cutMin limit (general form). -/
theorem const_cauchy_cutMin_limit (c1 c2 : Nat → Nat → Bool) :
    ((constCauchyCutSeq c1).cutMin (constCauchyCutSeq c2)).limit
    = cutMin c1 c2 := by
  rw [CauchyCutSeq.cutMin_limit,
      constCauchyCutSeq_limit c1, constCauchyCutSeq_limit c2]

/-- **Z3 scaling**: const Cauchy cutDouble limit. -/
theorem const_cauchy_cutDouble_limit (c : Nat → Nat → Bool) :
    ((constCauchyCutSeq c).cutDouble).limit = cutDouble c := by
  rw [CauchyCutSeq.cutDouble_limit, constCauchyCutSeq_limit]

/-- **Z3 scaling dual**: const Cauchy cutHalf limit. -/
theorem const_cauchy_cutHalf_limit (c : Nat → Nat → Bool) :
    ((constCauchyCutSeq c).cutHalf).limit = cutHalf c := by
  rw [CauchyCutSeq.cutHalf_limit, constCauchyCutSeq_limit]

/-- cutMid on Cauchy = cutHalf ∘ cutSum, lifted. -/
def CauchyCutSeq.cutMid (a b : CauchyCutSeq) : CauchyCutSeq :=
  (a.cutSum b).cutHalf

/-- Limit of cutMid of two Cauchy seqs = cutMid of limits. -/
theorem CauchyCutSeq.cutMid_limit (a b : CauchyCutSeq) :
    (a.cutMid b).limit = E213.Research.Real213.CutSum.cutMid a.limit b.limit := by
  show (a.cutSum b).cutHalf.limit
       = E213.Research.Real213.CutSum.cutHalf (E213.Research.Real213.CutSum.cutSum a.limit b.limit)
  rw [CauchyCutSeq.cutHalf_limit, CauchyCutSeq.cutSum_limit]

end E213.Research.Real213.CutSum
