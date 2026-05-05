import E213.Math.Analysis.DyadicSearch.DyadicBracket
import E213.Math.Analysis.CauchyComplete

/-!
# Research.Real213ConsistentOracle: oracle consistency as a typed
  protocol — the 213-native solution to Cauchy Case C.

## User insight (Phase J Sec 1)

The ghost of ZFC IVT comes from the myth that "c exists exactly somewhere."
213 rejects this, so instead of importing the oracle's *oscillation error
interval* as an external assumption, **the oracle itself must be shackled
with a protocol**.

## Definition

`ConsistentOracle db` guarantees:

- `oracle : DyadicOracle` — the steering wheel of bisection.
- `thresholdN m k : Nat` — the consistency threshold for query (m, k).
- `consistency` — for every step n with n ≥ thresholdN m k, the bracket
  midpoint cut at (m, k) is stable (if both n_1, n_2 are past the
  threshold, the midCut value is the same).

That is, a promise that the oracle does not retract its cut responses
after the threshold.

## Significance

Within this typed protocol, midSeq is Cauchy.  Exactly as the user
insight states: "the result is the trajectory itself, not the limit" —
ConsistentOracle is a type-level contract guaranteeing the trajectory
is sufficiently stable.
-/

namespace E213.Math.Analysis.DyadicSearch.ConsistentOracle

open E213.Firmware E213.Hypervisor
open E213.Math.Analysis.DyadicSearch.DyadicBracket
open E213.Math.Analysis.CauchyComplete (CauchyCutSeq)

/-- **ConsistentOracle**: an oracle protocol carrying its own
    consistency threshold function.

    The threshold `thresholdN m k` is the step count past which the
    bracket midpoint cut at query (m, k) is no longer flipped.

    Concrete instances supply the threshold formula based on
    target-cut parameters (db.lenNum, db.expE, m, k). -/
structure ConsistentOracle (db : DyadicBracket) where
  oracle : DyadicOracle
  /-- Per-query consistency threshold N(m, k).
      Recommended formula: lenNum * (m + k + 1) — linear in problem
      size, reliable since 2^N grows exponentially. -/
  thresholdN : Nat → Nat → Nat
  /-- For any two steps past the threshold, bracket midpoint cut at
      (m, k) is the same — sequence is stable. -/
  consistency : ∀ m k n1 n2,
    n1 ≥ thresholdN m k → n2 ≥ thresholdN m k →
    (DyadicBracket.bisectN oracle n1 db).midCut m k
    = (DyadicBracket.bisectN oracle n2 db).midCut m k

/-- **The 213-native IVT trajectory**: under a ConsistentOracle,
    the bracket midpoint sequence is a CauchyCutSeq.

    This is the formal payoff of Phase J: the IVT is no longer a
    point-existence claim but a Cauchy trajectory of dyadic
    midpoints, with explicit modulus baked in.  -/
def ConsistentOracle.toCauchyCutSeq {db : DyadicBracket}
    (co : ConsistentOracle db) : CauchyCutSeq where
  cs := fun n => (DyadicBracket.bisectN co.oracle n db).midCut
  N := co.thresholdN
  cauchy := co.consistency

/-- **Collapsed bracket gives a trivially-consistent oracle**.

    For any oracle, when the bracket starts collapsed (numA = numB),
    bisection cannot diverge — both leftHalf and rightHalf produce
    the same result.  The midpoint cut value at any (m, k) is
    invariant under n.  thresholdN = 0 (instant convergence). -/
def ConsistentOracle.collapsed
    (db : DyadicBracket) (h : db.numA = db.numB)
    (oracle : DyadicOracle) : ConsistentOracle db where
  oracle := oracle
  thresholdN := fun _ _ => 0
  consistency := by
    intro m k n1 n2 _ _
    rw [DyadicBracket.bisectN_collapsed_midCut_form oracle db h n1 m k,
        DyadicBracket.bisectN_collapsed_midCut_form oracle db h n2 m k]

end E213.Math.Analysis.DyadicSearch.ConsistentOracle
