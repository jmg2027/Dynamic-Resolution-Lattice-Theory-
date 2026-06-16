import E213.Lib.Math.Logic.RealDichotomyLLPO

/-!
# vein-C calibration: general real COMPARABILITY = LLPO

`RealDichotomyLLPO` pinned comparability against the constant `one`.  Here we
generalize to the comparability of two *arbitrary* corpus reals (cut functions):

  `comparability_imp_llpo : (∀ x y, cutLe x y ∨ cutLe y x) → LLPO`

i.e. "the corpus reals are not constructively totally ordered."

The forcing is a one-liner via route (b): instantiate the general comparability
hypothesis at `y := one` to recover the sign dichotomy
`RealDichotomyLLPO.RealDichotomy`, then apply the committed
`llpo_of_realDichotomy`.
-/

namespace E213.Lib.Math.Logic.RealComparabilityLLPO

open E213.Lib.Math.Logic (LLPO)
open E213.Lib.Math.NumberSystems.Real213.Core.CutPoset (cutLe)
open E213.Lib.Math.Logic.RealDichotomyLLPO (one RealDichotomy llpo_of_realDichotomy)

/-- A corpus real is a cut function `Nat → Nat → Bool`. -/
abbrev Cut : Type := Nat → Nat → Bool

/-- **General real comparability implies LLPO.**
    Comparability of *any two* corpus reals, instantiated at the constant `one`,
    is exactly the sign dichotomy `cutLe x one ∨ cutLe one x` of
    `RealDichotomyLLPO`, which already forces LLPO via the encoded cut.
    Hence the corpus reals are not constructively totally ordered. -/
theorem comparability_imp_llpo
    (hcomp : ∀ x y : Cut, cutLe x y ∨ cutLe y x) : LLPO :=
  llpo_of_realDichotomy (fun x => hcomp x one)

end E213.Lib.Math.Logic.RealComparabilityLLPO

-- purity probe (must be empty: "does not depend on any axioms")
#print axioms E213.Lib.Math.Logic.RealComparabilityLLPO.comparability_imp_llpo
