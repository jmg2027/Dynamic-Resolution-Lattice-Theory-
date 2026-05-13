import E213.Lib.Math.Analysis.Differentiation.PolySumDerivativeModulus
import E213.Lib.Math.Real213.Sum.CutSumComm

import E213.Lib.Math.Real213.Core.Core
import E213.Lib.Math.Real213.Sum.CutSum
import E213.Lib.Math.Real213.Sum.CutSumTest
/-!
# FluxCut
-1: **Cohomological flux structure** for 213 dyadic cuts.

In simplicial cohomology a 1-cochain assigns a value to each oriented
edge.  Sign emerges from edge *orientation*, not from arithmetic.

  FluxCut := { forward, backward : Cut }
  fluxNeg  = orientation reversal (involution)
  fluxAdd  = chain-group addition
  fluxSub  = formal difference (= add ∘ neg)

Bishop signed-cut pairing reinterpreted as flux on dyadic tree.
-/

namespace E213.Lib.Math.Analysis.FluxMVT.FluxCut

open E213.Lib.Math.Real213.Sum.CutSum (cutSum)
open E213.Theory E213.Lens
open E213.Lib.Math.Real213.Core.Core (Real213)
open E213.Lib.Math.Real213.Sum.CutSumComm (cutSum_comm)
open E213.Lib.Math.Real213.Sum.CutSumTest (constCut)

/-- Dyadic cut + cohomological orientation: forward / backward pair. -/
structure FluxCut where
  forward : Nat → Nat → Bool
  backward : Nat → Nat → Bool

namespace FluxCut

/-- Pure forward (positive) flux. -/
def ofCut (c : Nat → Nat → Bool) : FluxCut :=
  { forward := c, backward := constCut 0 1 }

/-- Zero flux. -/
def zero : FluxCut :=
  { forward := constCut 0 1, backward := constCut 0 1 }

/-- **Cohomological negation**: orientation reversal. -/
def neg (a : FluxCut) : FluxCut :=
  { forward := a.backward, backward := a.forward }

/-- **Flux addition** (chain-group). -/
def add (a b : FluxCut) : FluxCut :=
  { forward := cutSum a.forward b.forward,
    backward := cutSum a.backward b.backward }

/-- **Flux subtraction** = orientation reversal of second + addition. -/
def sub (a b : FluxCut) : FluxCut := add a (neg b)

/-- **Involution**: neg(neg a) = a. -/
theorem neg_neg (a : FluxCut) : neg (neg a) = a := by cases a; rfl

/-- **Anti-morphism**: neg distributes over add. -/
theorem neg_add (a b : FluxCut) :
    neg (add a b) = add (neg a) (neg b) := by cases a; cases b; rfl

/-- **Self-cancellation**: forward/backward of (sub a a) are
    pointwise equal — formal difference balances (∂² = 0 atomic). -/
theorem sub_self_balanced (a : FluxCut) (m k : Nat) :
    (sub a a).forward m k = (sub a a).backward m k := by
  show cutSum a.forward a.backward m k = cutSum a.backward a.forward m k
  exact cutSum_comm a.forward a.backward m k

/-- ofCut zero is FluxCut.zero. -/
theorem ofCut_zero : ofCut (constCut 0 1) = zero := rfl

/-- neg of pure forward = pure backward. -/
theorem neg_ofCut (c : Nat → Nat → Bool) :
    (ofCut c).neg = { forward := constCut 0 1, backward := c } := rfl

end FluxCut

end E213.Lib.Math.Analysis.FluxMVT.FluxCut
