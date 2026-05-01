import E213.Research.Real213.CutFnData
import E213.Research.Real213.SignedSum

/-!
# Research.Real213IVT: Intermediate Value Theorem (declarative form)

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

namespace E213.Research.Real213.IVT

open E213.Firmware E213.Hypervisor

/-- IVT hypothesis structure.

`f`: cut function, `a`, `b`: bracketing cuts, `f a sign positive`,
`f b sign negative` (or vice versa). -/
structure IVTHypothesis where
  f : (Nat → Nat → Bool) → (Nat → Nat → Bool)
  isLDD : LocallyDeterminedData f
  a : Nat → Nat → Bool
  b : Nat → Nat → Bool

/-- **IVT declarative statement**: existence of c under appropriate hypotheses.
    Constructive proof is bisection — a separate arc. -/
def IVTStatement (h : IVTHypothesis) : Prop :=
  ∃ c : Nat → Nat → Bool,
    -- framework-internal form of "a ≤ c ≤ b" and "f(c) ≈ 0"
    True  -- Placeholder — full statement needs cut order + zero approximation

end E213.Research.Real213.IVT
