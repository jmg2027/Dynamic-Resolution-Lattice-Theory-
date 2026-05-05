import E213.Math.Analysis.DyadicSearch.DyadicBracket
import E213.Math.Analysis.DyadicSearch.DyadicTrajectory
import E213.Math.Analysis.DyadicSearch.ConsistentOracle
import E213.Math.Analysis.CauchyComplete

/-!
# MinimalRootLens — trajectory-as-witness IVT readout

213-native form of the Intermediate Value Theorem:
the bisection trajectory *is* the root cut.  No locatedness, no
`Decidable` instance, no `propext`.  The "always-prefer-left" rule
is concretised by `signedLeftOracle`; the readout is the limit of
the midpoint sequence under `ConsistentOracle`'s typed protocol.

Design recorded in `research-notes/G31_minimal_root_lens.md`.

## Skeleton (this file)

  * `signedLeftOracle f` — always-prefer-left oracle from f's cut at
    unit precision (m=0, k=1).
  * `MinimalRootCut co` — trajectory readout
    (= `co.toCauchyCutSeq.limit`).
  * `MinimalRootCut_eq_at` — precision-stability past the modulus.
  * `MinimalRootCut_collapsed` — degenerate bracket sanity.

## Next milestone

`monotonicConsistentOracle f hMono db hAB` — yields full IVTRoot for
monotone f with sign change on [a, b].
-/

namespace E213.Math.Analysis.DyadicSearch.MinimalRootLens

open E213.Firmware E213.Hypervisor
open E213.Math.Analysis.DyadicSearch.DyadicBracket
open E213.Math.Analysis.DyadicSearch.DyadicTrajectory
  (alwaysTrue alwaysFalse)
open E213.Math.Analysis.DyadicSearch.ConsistentOracle
  (ConsistentOracle)
open E213.Math.Analysis.CauchyComplete (CauchyCutSeq)

/-- **signedLeftOracle**: always-prefer-left rule.

The oracle returns `f mid 0 1` — the cut value at unit precision
(m=0, k=1, the rational 0).  Interpretation: `true` ↔ "f(mid) ≥ 0
in cut sense" ↔ root is in the left half ↔ go left.

Bool-valued, no `Decidable` instance: the value comes directly out
of f's cut representation. -/
def signedLeftOracle (f : (Nat → Nat → Bool) → (Nat → Nat → Bool)) :
    DyadicOracle :=
  fun mid => f mid 0 1

/-- Sanity: for the constantly-true cut function, `signedLeftOracle`
    reduces to `alwaysTrue` (every step takes left half). -/
theorem signedLeftOracle_constTrue :
    signedLeftOracle (fun _ _ _ => true) = alwaysTrue := rfl

/-- Sanity: for the constantly-false cut function, `signedLeftOracle`
    reduces to `alwaysFalse` (every step takes right half). -/
theorem signedLeftOracle_constFalse :
    signedLeftOracle (fun _ _ _ => false) = alwaysFalse := rfl

/-- **MinimalRootCut**: trajectory readout under a `ConsistentOracle`.

Given a typed-protocol witness `co : ConsistentOracle db`, the
minimal-root cut is the limit of the bracket midpoint sequence.
This is the 213-native form of IVT — the cut *is* the trajectory's
stabilised midpoint, not an externally-postulated point.

The choice of oracle is up to the protocol witness; for monotone
`f` with a sign change the canonical choice is `signedLeftOracle f`,
giving the leftmost (minimal) root. -/
def MinimalRootCut {db : DyadicBracket} (co : ConsistentOracle db) :
    Nat → Nat → Bool :=
  co.toCauchyCutSeq.limit

/-- **Precision stability**: past the consistency threshold, the
    minimal-root cut at `(m, k)` equals any midCut readout at depth
    `n ≥ co.thresholdN m k`.

Direct corollary of `CauchyCutSeq.limit_eq_at`. -/
theorem MinimalRootCut_eq_at {db : DyadicBracket}
    (co : ConsistentOracle db) (m k n : Nat)
    (hn : n ≥ co.thresholdN m k) :
    MinimalRootCut co m k
    = (DyadicBracket.bisectN co.oracle n db).midCut m k :=
  co.toCauchyCutSeq.limit_eq_at m k n hn

/-- **Collapsed-bracket sanity**: when the starting bracket is degenerate
    (numA = numB), the minimal-root cut at any `(m, k)` reduces to the
    constant midCut form `decide (db.numA * k ≤ 2^db.expE * m)` —
    the unique cut that the trajectory could possibly converge to.

Closed via `bisectN_collapsed_midCut_form` at depth = thresholdN. -/
theorem MinimalRootCut_collapsed {db : DyadicBracket}
    (co : ConsistentOracle db) (h : db.numA = db.numB) (m k : Nat) :
    MinimalRootCut co m k
    = decide (db.numA * k ≤ 2^db.expE * m) := by
  rw [MinimalRootCut_eq_at co m k (co.thresholdN m k) (Nat.le_refl _)]
  exact DyadicBracket.bisectN_collapsed_midCut_form
          co.oracle db h (co.thresholdN m k) m k

end E213.Math.Analysis.DyadicSearch.MinimalRootLens

