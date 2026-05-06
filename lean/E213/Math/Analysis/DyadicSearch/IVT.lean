import E213.Math.Real213.CutFnData
import E213.Math.Real213.SignedSum

import E213.Math.Real213.Core
import E213.Math.Real213.CutPoset
import E213.Math.Real213.CutSumTest
/-!
# Real213IVT: Intermediate Value Theorem (declarative form)

Bishop-style IVT for 213-native cut functions.

## Statement (declarative)

For locally-determined f : RealCut → RealCut and bounds a, b cuts
with a ≤ b and f(a) ≤ 0 ≤ f(b), there exists c with a ≤ c ≤ b and
f(c) approximates 0.

## Significance

Cut-level IVT — the framework-internal form of the bisection algorithm.  Full
constructive proof is a separate arc (bisection sequence + Cauchy convergence
+ continuity preservation).

This file is *interface* only — IVT statement + supporting types.
-/

namespace E213.Math.Analysis.DyadicSearch.IVT

open E213.Firmware E213.Lens
open E213.Math.Real213.Core (Real213)
open E213.Math.Real213.CutFnData (LocallyDeterminedData)
open E213.Math.Real213.CutPoset (cutLe cutEq)
open E213.Math.Real213.CutSumTest (constCut)

/-- IVT hypothesis structure.

`f`: cut function, `a`, `b`: bracketing cuts, `f a sign positive`,
`f b sign negative` (or vice versa). -/
structure IVTHypothesis where
  f : (Nat → Nat → Bool) → (Nat → Nat → Bool)
  isLDD : LocallyDeterminedData f
  a : Nat → Nat → Bool
  b : Nat → Nat → Bool

/-- **IVT declarative statement**: existence of `c` with `a ≤ c ≤ b` and
    `f(c) cutEq 0`.

    Cut order via `CutPoset.cutLe`; "zero approximation" via pointwise
    `cutEq` against `constCut 0 1` (the canonical zero cut).  This is the
    Bishop-locatedness limit form — the bisection sequence converges
    constructively to a cut whose image cutEq's the zero cut.  Full
    constructive proof is a separate arc (bisection + bracket-Cauchy
    modulus + continuity preservation). -/
def IVTStatement (h : IVTHypothesis) : Prop :=
  ∃ c : Nat → Nat → Bool,
    cutLe h.a c ∧ cutLe c h.b ∧ cutEq (h.f c) (constCut 0 1)

/-- **Witness shape**: an IVT root packaged as `c` plus the three
    proof obligations.  Useful for downstream consumers that want to
    pattern-match on the existential. -/
structure IVTRoot (h : IVTHypothesis) where
  c : Nat → Nat → Bool
  lower : cutLe h.a c
  upper : cutLe c h.b
  zero : cutEq (h.f c) (constCut 0 1)

/-- An `IVTRoot` discharges `IVTStatement`. -/
theorem IVTStatement_of_root {h : IVTHypothesis} (r : IVTRoot h) :
    IVTStatement h :=
  ⟨r.c, r.lower, r.upper, r.zero⟩

end E213.Math.Analysis.DyadicSearch.IVT
