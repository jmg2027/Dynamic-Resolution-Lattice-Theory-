import E213.Lib.Math.Real213.ChainToCut
import E213.Lib.Math.Analysis.CauchyProj

/-!
# Analysis.ChainCauchy — ChainToCut + CauchyProj integration

Natural composition of two bridges:
  - `ChainToCut`:  Raw chain → Real213 cut.
  - `CauchyProj`:  CauchyCutSeq → CauchyCutSeq (constant at limit).

Composition: Raw chain → constant Cauchy seq at the corresponding
cut.

Demonstrates catalog coherence — the bridges compose freely with
zero added axioms.  `Lens/Number/Nat213/*` (Method A chain) →
Real213 cut → Cauchy seq is a natural chain.
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

/-- Limit is exactly `chainToCut` (rfl). -/
theorem chainCauchyCutSeq_limit (r : Raw) :
    (chainCauchyCutSeq r).limit = chainToCut r := rfl

/-- `chainCauchyCutSeq` is a fixed point of `cauchyProj` (rfl).
    The chain image is always constant-at-limit. -/
theorem cauchyProj_chainCauchyCutSeq (r : Raw) :
    cauchyProj (chainCauchyCutSeq r) = chainCauchyCutSeq r := rfl

end E213.Lib.Math.Analysis.ChainCauchy
