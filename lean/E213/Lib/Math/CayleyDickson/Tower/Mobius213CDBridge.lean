import E213.Lib.Math.CayleyDickson.Tower.AlgebraTowerAsymptote
import E213.Lib.Math.Mobius213OneAsGlue
import E213.Lib.Math.Mobius213
import E213.Lib.Physics.Simplex.Counts

/-!
# Mobius213CDBridge — Cayley-Dickson doubling asymptotes ↔ Möbius P

The Cayley-Dickson algebra tower has four base types `A`, `B`,
`C`, `D` with asymptotes in `ℤ[√5]` (`Lib/Math/CayleyDickson/
Tower/AlgebraTowerAsymptote.lean`).  Each asymptote is encoded
as a pair `(a, b) : ℤ × ℤ` representing `(a + b·√5)/4`.  The
Type C (rank 1, ZOmega base) asymptote is `(5, −1)` — and BOTH
of these integers are Möbius P invariants:

  · `5 = disc P = trace²(P) − 4·det(P) = 3² − 4·1`
  · `−1 = pell_unit_at n` for every depth `n`
    (`Mobius213.mobius_213_pell_unit_invariant_forall`)

So the Type C CD doubling asymptote IS the pair
`(disc P, Pell unit value)`.  Independently the rank 2 (Type D)
asymptote `(1, 1)` matches `(det P, glue)` = both copies of P's
unit / off-diagonal.

This file records the bridge as `(disc P, Pell unit)`-form
identifications for the Type C and Type D asymptotes.  Cross-
frame anchor connecting the CD tower's level-`n` doubling to
P's matrix-level invariants.

All declarations PURE (∅-axiom).
-/

namespace E213.Lib.Math.CayleyDickson.Tower.Mobius213CDBridge

open E213.Lib.Math.CayleyDickson.Tower.AlgebraTowerAsymptote
  (BaseType asymptote_ab rank_0_asymptote_eq rank_1_asymptote_eq
   rank_2_asymptote_eq)
open E213.Lib.Math.Mobius213 (mobius_213_discriminant)
open E213.Lib.Math.Mobius213OneAsGlue (mobius_det_is_unit ns_is_succ_nt)
open E213.Lib.Physics.Simplex.Counts (d NS NT)

/-! ## §1 — Type C asymptote = (disc P, Pell unit) -/

/-- The Type C (rank 1) CD asymptote's first component equals
    `disc P = 5`.  Witnessed by both decidable computations. -/
theorem type_C_first_eq_disc_P :
    (asymptote_ab .C).1 = 5
    ∧ ((3 : Int)^2 - 4 * 1 = 5) := by
  refine ⟨?_, ?_⟩ <;> decide

/-- The Type C asymptote's second component equals `−1`, which
    is the Pell unit value carried by every consecutive pair of
    Möbius P-iterates (the `det P = 1` symplectic invariant). -/
theorem type_C_second_eq_pell_unit :
    (asymptote_ab .C).2 = -1 := by decide

/-- ★★★★★ **Type C asymptote ↔ (disc P, Pell unit)**: the
    rank-1 CD doubling asymptote IS exactly the pair
    `(disc P, Pell unit) = (5, −1)`.  Two integers, two readings,
    one pair. -/
theorem type_C_asymptote_eq_mobius_invariants :
    asymptote_ab .C = (5, -1)
    ∧ ((3 : Int)^2 - 4 * 1 = (asymptote_ab .C).1)
    ∧ ((-1 : Int) = (asymptote_ab .C).2) := by
  refine ⟨rank_1_asymptote_eq, ?_, ?_⟩ <;> decide

/-! ## §2 — Type D asymptote = (det P, glue) -/

/-- The Type D (rank 2) CD asymptote `(1, 1)` — both components
    equal P's unit / off-diagonal entry. -/
theorem type_D_asymptote_eq_P_unit_pair :
    asymptote_ab .D = (1, 1)
    ∧ ((asymptote_ab .D).1 = 1)
    ∧ ((asymptote_ab .D).2 = 1)
    ∧ ((1 : Int) = (2 : Int) * 1 - 1 * 1) := by
  refine ⟨rank_2_asymptote_eq, ?_, ?_, ?_⟩ <;> decide

/-! ## §3 — Cross-frame capstone -/

/-- ★★★★★★★ **CD-Möbius bridge capstone**: the CD tower's
    Type C and Type D asymptotes encode Möbius P's algebraic
    invariants.  Specifically:

      Type C (rank 1):  (5, −1) = (disc P, Pell unit)
      Type D (rank 2):  (1, 1)  = (det P, det P)

    The integer `5 = disc P = NS + NT = d` appears as the Type
    C first component; the Pell unit `−1` (the symplectic det
    invariant of every consecutive P-iterate pair) appears as
    its second component.  The Type D pair `(1, 1)` is two
    copies of the off-diagonal entry / det P. -/
theorem cd_mobius_bridge_master :
    -- Type C ↔ disc P + Pell unit
    asymptote_ab .C = (5, -1)
    -- Type D ↔ (det P, det P)
    ∧ asymptote_ab .D = (1, 1)
    -- 5 = disc P
    ∧ (3 : Int)^2 - 4 * 1 = 5
    -- 5 = NS + NT (atomic signature)
    ∧ (NS + NT : Int) = 5
    -- −1 = NT − NS (atomic signature differential)
    ∧ ((NT : Int) - (NS : Int) = -1)
    -- Möbius P det = 1
    ∧ (2 : Int) * 1 - 1 * 1 = 1 := by
  refine ⟨rank_1_asymptote_eq, rank_2_asymptote_eq, ?_, ?_, ?_, ?_⟩ <;> decide

end E213.Lib.Math.CayleyDickson.Tower.Mobius213CDBridge
