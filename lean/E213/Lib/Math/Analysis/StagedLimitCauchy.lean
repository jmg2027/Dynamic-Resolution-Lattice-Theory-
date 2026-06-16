import E213.Lib.Math.Analysis.CauchyComplete
import E213.Meta.StagedLimit

/-!
# CauchyCutSeq as a StagedLimit (∅-axiom)

The Real213 Cauchy-completeness limit (`Analysis.CauchyComplete.CauchyCutSeq`) is
a `Meta.StagedLimit` instance: coordinate `(m,k)`, value `Bool`, modulus `N m k`.
`cauchy_limit_eq_late` routes the concrete `CauchyCutSeq.limit_eq_at` through the
abstract `StagedLimit.limit_eq_late` — the **generic-consumer** demonstration that
the stabilization map has real downstream work, not a vacuous container.
-/

namespace E213.Lib.Math.Analysis.StagedLimitCauchy

open E213.Lib.Math.Analysis.CauchyComplete (CauchyCutSeq)
open E213.Meta.StagedLimit (StagedLimit)

/-- A Cauchy sequence of cuts as a staged limit over coordinate `(m,k)`. -/
def cauchyToStagedLimit (ccs : CauchyCutSeq) : StagedLimit (Nat × Nat) Bool where
  s := fun i c => ccs.cs i c.1 c.2
  N := fun c => ccs.N c.1 c.2
  stable := fun c i j hi hj => ccs.cauchy c.1 c.2 i j hi hj

/-- The cut-level limit IS the staged limit's `limit` (definitional). -/
theorem cauchy_limit_eq_staged (ccs : CauchyCutSeq) (m k : Nat) :
    ccs.limit m k = (cauchyToStagedLimit ccs).limit (m, k) := rfl

/-- ★★ `CauchyCutSeq.limit_eq_at` recovered through the abstract schema: the
    Real213 completeness limit equals every late stage *via* `StagedLimit`. -/
theorem cauchy_limit_eq_late (ccs : CauchyCutSeq) (m k i : Nat)
    (hi : ccs.N m k ≤ i) : ccs.limit m k = ccs.cs i m k :=
  (cauchyToStagedLimit ccs).limit_eq_late (m, k) i hi

end E213.Lib.Math.Analysis.StagedLimitCauchy
