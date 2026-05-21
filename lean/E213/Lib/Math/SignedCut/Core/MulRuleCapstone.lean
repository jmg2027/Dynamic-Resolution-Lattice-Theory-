import E213.Lib.Math.SignedCut.CD.CDMulRule
import E213.Lib.Math.SignedCut.CD.CDLevelOps
import E213.Lib.Math.SignedCut.Hurwitz.HurwitzCeiling

/-!
# CD Multiplication Rule + Hurwitz Ceiling Capstone (∅-axiom)

3 cluster witnesses + total bundle.  Closes the two PR #62
post-G36 open items:

  * **Multiplication-rule parametrisation** of the CD tower
    (sign vs complex distinction at level 1).
  * **Hurwitz-style ceiling proof** at level 25 on d=5
    level-0 base (= N_U count-Lens readout).
-/

namespace E213.Lib.Math.SignedCut.Core.MulRuleCapstone

open E213.Lib.Math.SignedCut.CD.CDMulRule
  (CDRule signMul complexMul cdrule_neq mulrules_im_agree)
open E213.Lib.Math.SignedCut.CD.CDLevelOps
  (signMul_matches_signedMul signMul_matches_signedMul_snd
   complexMul_matches_cMul_im rules_share_cross_term)
open E213.Lib.Math.SignedCut.Hurwitz.HurwitzCeiling
  (dim_tower_through_5 n_u_finite ceiling_param
   hurwitz_d5_ceiling n_u_value_closed)
open E213.Lib.Math.Real213.Sum.CutSum (cutSum)
open E213.Lib.Math.Real213.Mul.CutMul (cutMul)
open E213.Lib.Math.SignedCut.CD.CDTowerLevel (levelDim)

/-- ★ **Mul-rule witness**. -/
theorem mulrule_witness (a b c d : Nat → Nat → Bool) :
    ¬ (CDRule.signRule = CDRule.complexRule)
    ∧ (signMul a b c d).2 = (complexMul a b c d).2
    ∧ (signMul a b c d).1 = cutSum (cutMul a c) (cutMul b d) :=
  ⟨cdrule_neq, mulrules_im_agree a b c d, rfl⟩

/-- ★ **Layer-bridge witness**. -/
theorem layerBridge_witness (a b c d : Nat → Nat → Bool) :
    (signMul a b c d).1 = cutSum (cutMul a c) (cutMul b d)
    ∧ (signMul a b c d).2 = cutSum (cutMul a d) (cutMul b c)
    ∧ (complexMul a b c d).2 = cutSum (cutMul a d) (cutMul b c) :=
  ⟨signMul_matches_signedMul a b c d,
   signMul_matches_signedMul_snd a b c d,
   complexMul_matches_cMul_im a b c d⟩

/-- ★ **Hurwitz-d5 ceiling witness**. -/
theorem hurwitz_witness :
    levelDim 25 = 33554432
    ∧ (5 : Nat) ^ 25 = 298023223876953125
    ∧ (5 : Nat) * 5 = 25 :=
  ⟨hurwitz_d5_ceiling.1, n_u_value_closed, ceiling_param⟩

/-- ★★★ **Total witness** ★★★ — mul-rule + bridge + ceiling. -/
theorem total_witness (a b c d : Nat → Nat → Bool) :
    (signMul a b c d).1 = cutSum (cutMul a c) (cutMul b d)
    ∧ (complexMul a b c d).1 = cutMul a c
    ∧ levelDim 25 = 33554432
    ∧ (5 : Nat) ^ 25 = 298023223876953125 :=
  ⟨rfl, rfl, hurwitz_d5_ceiling.1, n_u_value_closed⟩

end E213.Lib.Math.SignedCut.Core.MulRuleCapstone
