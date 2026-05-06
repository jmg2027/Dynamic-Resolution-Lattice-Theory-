import E213.Math.Analysis.DyadicSearch.DyadicBracket
import E213.Math.Analysis.DyadicSearch.DyadicTrajectory
import E213.Math.Analysis.DyadicSearch.ConsistentOracle
import E213.Math.Analysis.DyadicSearch.IVT
import E213.Math.Analysis.CauchyComplete
import E213.Math.Real213.CutFnData

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

open E213.Firmware E213.Lens
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

/-- **signedRightOracle**: dual policy — used for the *opposite*
    sign convention (`f leftCut 0 1 = true`, `f rightCut 0 1 = false`,
    i.e., f *increasing* with `f(a) ≤ 0 ≤ f(b)`).

The oracle returns `!(f mid 0 1)`.  Interpretation: `true` ↔ go left
↔ `f(mid) > 0` ↔ root is in `[a, mid]` (left half).

Together with `signedLeftOracle`, this enumerates the two boundary
preferences for the f-derived bisection trajectory; the choice of
oracle *is itself a lens* (the meta-policy lens).  In d=5 finite
structure, each `(m', k')`-precision query gives a candidate
oracle, so the oracle space is finitely indexed. -/
def signedRightOracle (f : (Nat → Nat → Bool) → (Nat → Nat → Bool)) :
    DyadicOracle :=
  fun mid => !(f mid 0 1)

/-- Sanity: for the constantly-false cut function, `signedRightOracle`
    reduces to `alwaysTrue`. -/
theorem signedRightOracle_constFalse :
    signedRightOracle (fun _ _ _ => false) = alwaysTrue := rfl

/-- Sanity: for the constantly-true cut function, `signedRightOracle`
    reduces to `alwaysFalse`. -/
theorem signedRightOracle_constTrue :
    signedRightOracle (fun _ _ _ => true) = alwaysFalse := rfl

/-- The two policy oracles are pointwise Bool-negations: under any
    midpoint cut, `signedLeftOracle f mid = !(signedRightOracle f mid)`.

Demonstrates the **meta-policy duality** structurally — the choice
between left-prefer and right-prefer at the boundary is a single
Bool, exposed as a lens. -/
theorem signedLeftOracle_eq_not_signedRightOracle
    (f : (Nat → Nat → Bool) → (Nat → Nat → Bool)) (mid : Nat → Nat → Bool) :
    signedLeftOracle f mid = !(signedRightOracle f mid) := by
  show f mid 0 1 = !(!(f mid 0 1))
  cases f mid 0 1 <;> rfl

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

/-! ### Bracket bounds on the trajectory readout

The minimal-root cut is squeezed between the starting bracket's
endpoints — `db.leftCut ≤ MinimalRootCut co ≤ db.rightCut`.  These
follow directly from the bracket-containment lemmas
`bisectN_midCut_above_left` / `bisectN_midCut_below_right` (already
strict ∅-axiom in `DyadicBracket.lean`) at the threshold depth. -/

open E213.Math.Real213.CutPoset (cutLe)

/-- **Lower bound**: `db.leftCut ≤ MinimalRootCut co` (cut-≤ form).

Direct corollary of `bisectN_midCut_above_left` at the threshold
depth, via `MinimalRootCut_eq_at`. -/
theorem MinimalRootCut_lower {db : DyadicBracket}
    (co : ConsistentOracle db) :
    cutLe db.leftCut (MinimalRootCut co) := by
  intro m k h
  rw [MinimalRootCut_eq_at co m k (co.thresholdN m k) (Nat.le_refl _)] at h
  exact DyadicBracket.bisectN_midCut_above_left
          co.oracle (co.thresholdN m k) db m k h

/-- **Upper bound**: `MinimalRootCut co ≤ db.rightCut` (cut-≤ form).

Direct corollary of `bisectN_midCut_below_right` at the threshold
depth, via `MinimalRootCut_eq_at`. -/
theorem MinimalRootCut_upper {db : DyadicBracket}
    (co : ConsistentOracle db) :
    cutLe (MinimalRootCut co) db.rightCut := by
  intro m k h
  exact (MinimalRootCut_eq_at co m k (co.thresholdN m k) (Nat.le_refl _)).trans
    (DyadicBracket.bisectN_midCut_below_right
      co.oracle (co.thresholdN m k) db m k h)

/-! ### IVTRoot bridge

Combine the trajectory readout with a `zero` certificate to obtain
the full `IVTRoot`.  Lower / upper come automatically from the
trajectory's bracket-containment; the zero field is delivered by
the caller (e.g., the future monotone-IVT certificate). -/

open E213.Math.Real213.CutFnData (LocallyDeterminedData)
open E213.Math.Real213.CutPoset (cutEq)
open E213.Math.Real213.CutSumTest (constCut)
open E213.Math.Analysis.DyadicSearch.IVT (IVTHypothesis IVTRoot)

/-- **IVTRoot from a ConsistentOracle + zero proof**.

For any starting bracket `db` and `f` locally-determined, a
`ConsistentOracle db` gives the candidate root `c := MinimalRootCut co`
and the bracket bounds `lower / upper`.  The caller supplies the
`zero` certificate `cutEq (f c) (constCut 0 1)` (the IVT content
proper) and gets a full `IVTRoot` for the IVTHypothesis whose
endpoint cuts are `db.leftCut` / `db.rightCut`. -/
def IVTRoot.fromConsistentOracle
    {f : (Nat → Nat → Bool) → (Nat → Nat → Bool)}
    (lf : LocallyDeterminedData f) {db : DyadicBracket}
    (co : ConsistentOracle db)
    (hzero : cutEq (f (MinimalRootCut co)) (constCut 0 1)) :
    IVTRoot { f := f, isLDD := lf,
              a := db.leftCut, b := db.rightCut } where
  c := MinimalRootCut co
  lower := MinimalRootCut_lower co
  upper := MinimalRootCut_upper co
  zero := hzero

end E213.Math.Analysis.DyadicSearch.MinimalRootLens

