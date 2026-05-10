import E213.Lib.Math.Real213.ChainToCut
import E213.Lib.Math.Analysis.CauchyProj

/-!
# Analysis.ChainCauchy — ChainToCut + CauchyProj integration

세션의 두 bridge 의 자연스러운 결합:
  - `ChainToCut`:  Raw chain → Real213 cut.
  - `CauchyProj`:  CauchyCutSeq → CauchyCutSeq (constant at limit).

결합: Raw chain → constant Cauchy seq at corresponding cut.

이게 catalog 의 정합성 입증 — bridge 들이 free 로 compose, 추가 axiom 0.
Theory/Closed/* (Nat) → Real213 cut → Cauchy seq 의 자연스러운 chain.
-/

namespace E213.Lib.Math.Analysis.ChainCauchy

open E213.Theory
open E213.Lib.Math.Analysis.CauchyComplete (CauchyCutSeq constCauchyCutSeq)
open E213.Lib.Math.Analysis.CauchyProj (cauchyProj)
open E213.Lib.Math.Real213.ChainToCut (chainToCut)

/-- Chain → constant Cauchy seq at chain's cut.  Bridge composition:
    `Raw → (Nat → Nat → Bool) → CauchyCutSeq`. -/
def chainCauchyCutSeq (r : Raw) : CauchyCutSeq :=
  constCauchyCutSeq (chainToCut r)

/-- limit 이 정확히 chainToCut.  rfl. -/
theorem chainCauchyCutSeq_limit (r : Raw) :
    (chainCauchyCutSeq r).limit = chainToCut r := rfl

/-- chainCauchyCutSeq 는 cauchyProj 의 fixed point.  rfl.  Chain image
    가 항상 constant-at-limit 형태이기 때문. -/
theorem cauchyProj_chainCauchyCutSeq (r : Raw) :
    cauchyProj (chainCauchyCutSeq r) = chainCauchyCutSeq r := rfl

end E213.Lib.Math.Analysis.ChainCauchy
