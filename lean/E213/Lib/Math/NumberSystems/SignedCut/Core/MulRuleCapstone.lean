import E213.Lib.Math.NumberSystems.SignedCut.CD.CDMulRule
import E213.Lib.Math.NumberSystems.SignedCut.CD.CDLevelOps

/-!
# CD Multiplication Rule Capstone (∅-axiom)

Cluster witnesses + total bundle for the CD-tower multiplication
rule:

  * **Multiplication-rule parametrisation** of the CD tower
    (sign vs complex distinction at level 1).
  * **Layer bridge** from the parametrised rule to the underlying
    Cut substrate operations.
-/

namespace E213.Lib.Math.NumberSystems.SignedCut.Core.MulRuleCapstone

open E213.Lib.Math.NumberSystems.SignedCut.CD.CDMulRule
  (CDRule signMul complexMul cdrule_neq mulrules_im_agree)
open E213.Lib.Math.NumberSystems.SignedCut.CD.CDLevelOps
  (signMul_matches_signedMul signMul_matches_signedMul_snd
   complexMul_matches_cMul_im rules_share_cross_term)
open E213.Lib.Math.NumberSystems.Real213.Sum.CutSum (cutSum)
open E213.Lib.Math.NumberSystems.Real213.Mul.CutMul (cutMul)

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

/-- ★★★ **Total witness** ★★★ — mul-rule + layer bridge. -/
theorem total_witness (a b c d : Nat → Nat → Bool) :
    (signMul a b c d).1 = cutSum (cutMul a c) (cutMul b d)
    ∧ (complexMul a b c d).1 = cutMul a c :=
  ⟨rfl, rfl⟩

end E213.Lib.Math.NumberSystems.SignedCut.Core.MulRuleCapstone
