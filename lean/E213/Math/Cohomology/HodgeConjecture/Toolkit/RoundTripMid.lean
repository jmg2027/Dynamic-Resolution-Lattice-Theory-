import E213.Math.Cohomology.HodgeConjecture.Toolkit.Primitives

/-!
# Hodge Toolkit T2 mid-strata — round-trip on (5, 2) and (5, 3)

Companion to `RoundTrip.lean`: covers the middle strata of Δ⁴
(2¹⁰ patterns each × 10 indices = 10240 evaluations per `decide`).

Heavy `decide` files isolated here so the rest of the toolkit builds
fast.  STRICT ∅-AXIOM.
-/

namespace E213.Math.Cohomology.HodgeConjecture.Toolkit.RoundTripMid

open E213.Math.Cohomology.Cochain.Core (Cochain)
open E213.Math.Cohomology.HodgeConjecture.Toolkit.Primitives (support fromList)
open E213.Physics.Simplex.Counts (binom)

/-- (5, 2) pattern: 10-bit cochain (one bit per edge). -/
def patt_5_2 (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool) : Cochain 5 2 :=
  fun i =>
    if i.val = 0 then b0
    else if i.val = 1 then b1
    else if i.val = 2 then b2
    else if i.val = 3 then b3
    else if i.val = 4 then b4
    else if i.val = 5 then b5
    else if i.val = 6 then b6
    else if i.val = 7 then b7
    else if i.val = 8 then b8
    else b9

/-- (5, 3) pattern: 10-bit cochain (one bit per triangle). -/
def patt_5_3 (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool) : Cochain 5 3 :=
  fun i =>
    if i.val = 0 then b0
    else if i.val = 1 then b1
    else if i.val = 2 then b2
    else if i.val = 3 then b3
    else if i.val = 4 then b4
    else if i.val = 5 then b5
    else if i.val = 6 then b6
    else if i.val = 7 then b7
    else if i.val = 8 then b8
    else b9

/-- Round-trip on every (5, 2) pattern (1024 × 10 = 10240 cases). -/
theorem round_trip_5_2 :
    ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool, ∀ j : Fin (binom 5 2),
      fromList (support (patt_5_2 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9)) j
        = (patt_5_2 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9) j := by decide

/-- Round-trip on every (5, 3) pattern (1024 × 10 = 10240 cases). -/
theorem round_trip_5_3 :
    ∀ b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool, ∀ j : Fin (binom 5 3),
      fromList (support (patt_5_3 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9)) j
        = (patt_5_3 b0 b1 b2 b3 b4 b5 b6 b7 b8 b9) j := by decide

end E213.Math.Cohomology.HodgeConjecture.Toolkit.RoundTripMid
