import E213.Math.Cohomology.HodgeConjecture.Toolkit.Primitives

import E213.Math.Cohomology.Cochain.Core
import E213.Physics.Simplex.Counts
/-!
# Hodge Toolkit T2 — round-trip `fromList ∘ support = id`

`fromList (support σ) j = σ j` pointwise.  STRICT ∅-AXIOM via
`decide` over Bool-pattern enumeration of each Δ⁴ stratum.

Strata covered: (5, 0), (5, 1), (5, 4), (5, 5).  Middle strata
(5, 2), (5, 3) have 2¹⁰ patterns each — deferred to follow-up.
-/

namespace E213.Math.Cohomology.HodgeConjecture.Toolkit.RoundTrip

open E213.Math.Cohomology.Cochain.Core (Cochain)
open E213.Math.Cohomology.HodgeConjecture.Toolkit.Primitives (support fromList)
open E213.Physics.Simplex.Counts (binom)

/-- (5, 0) pattern. -/
def patt_5_0 (b : Bool) : Cochain 5 0 := fun _ => b

/-- (5, 5) pattern. -/
def patt_5_5 (b : Bool) : Cochain 5 5 := fun _ => b

/-- (5, 1) pattern: 5-bit cochain (one bit per vertex). -/
def patt_5_1 (b0 b1 b2 b3 b4 : Bool) : Cochain 5 1 :=
  fun i =>
    if i.val = 0 then b0
    else if i.val = 1 then b1
    else if i.val = 2 then b2
    else if i.val = 3 then b3
    else b4

/-- (5, 4) pattern: 5-bit cochain (one bit per face). -/
def patt_5_4 (b0 b1 b2 b3 b4 : Bool) : Cochain 5 4 :=
  fun i =>
    if i.val = 0 then b0
    else if i.val = 1 then b1
    else if i.val = 2 then b2
    else if i.val = 3 then b3
    else b4

/-- Round-trip on every (5, 0) pattern (2 cases). -/
theorem round_trip_5_0 :
    ∀ b : Bool, ∀ j : Fin (binom 5 0),
      fromList (support (patt_5_0 b)) j = (patt_5_0 b) j := by decide

/-- Round-trip on every (5, 5) pattern (2 cases). -/
theorem round_trip_5_5 :
    ∀ b : Bool, ∀ j : Fin (binom 5 5),
      fromList (support (patt_5_5 b)) j = (patt_5_5 b) j := by decide

/-- Round-trip on every (5, 1) pattern (32 × 5 = 160 cases). -/
theorem round_trip_5_1 :
    ∀ b0 b1 b2 b3 b4 : Bool, ∀ j : Fin (binom 5 1),
      fromList (support (patt_5_1 b0 b1 b2 b3 b4)) j
        = (patt_5_1 b0 b1 b2 b3 b4) j := by decide

/-- Round-trip on every (5, 4) pattern (32 × 5 = 160 cases). -/
theorem round_trip_5_4 :
    ∀ b0 b1 b2 b3 b4 : Bool, ∀ j : Fin (binom 5 4),
      fromList (support (patt_5_4 b0 b1 b2 b3 b4)) j
        = (patt_5_4 b0 b1 b2 b3 b4) j := by decide

/-- ★★★★★ Round-trip capstone — STRICT ∅-AXIOM, 4 strata of Δ⁴. -/
theorem round_trip_capstone :
    (∀ b j, fromList (support (patt_5_0 b)) j = (patt_5_0 b) j)
    ∧ (∀ b j, fromList (support (patt_5_5 b)) j = (patt_5_5 b) j)
    ∧ (∀ b0 b1 b2 b3 b4 j,
         fromList (support (patt_5_1 b0 b1 b2 b3 b4)) j
           = (patt_5_1 b0 b1 b2 b3 b4) j)
    ∧ (∀ b0 b1 b2 b3 b4 j,
         fromList (support (patt_5_4 b0 b1 b2 b3 b4)) j
           = (patt_5_4 b0 b1 b2 b3 b4) j) :=
  ⟨round_trip_5_0, round_trip_5_5, round_trip_5_1, round_trip_5_4⟩

end E213.Math.Cohomology.HodgeConjecture.Toolkit.RoundTrip
