import E213.Lib.Math.CayleyDickson.Tower.ExceptionalTraceSeed
import E213.Lib.Math.CayleyDickson.Tower.DiscForcingObstruction

/-!
# Seed re-entry: the same residue at every scale (disc = trace = field disc)

The 213 expansion engine: a distinction leaves a *unit residue*, and that
residue is the next operand — a gapless self-similar spiral, no exterior,
the meta-layer just another step of the same operation
(`diag_self_applies`).  At the level of the exceptional seeds this is
literally visible: the seed *number* re-enters as its own operand at each
scale of the construction.

Take `E₈`, seed `√(NS+NT) = √5`.  The number `5 = NS+NT` appears as:

  * **2D matrix scale** — `disc P = trace² − 4·det = 3² − 4 = 5`
    (the Möbius `P = [[2,1],[1,1]]`);
  * **number-field scale** — `fundDisc ℚ(√5) = 5` (since `5 ≡ 1 mod 4`);
  * **4D quaternion scale** — `(2·trace(g₅) + 1)² = 5` (the order-`5`
    icosian trace, `ExceptionalTraceSeed`).

One residue, three scales — not three facts but the same `5 = NS+NT` seen
one scale up each time.  That is the engine: the seed is fed back as the
operand of the next construction, gaplessly, with no outside to draw a
different number from.

For the other two seeds the *fundamental* discriminant of the quadratic
field is:

  * `E₆`: `fundDisc ℚ(√(−NS)) = −NS = −3` (`−3 ≡ 1 mod 4`);
  * `E₇`: `fundDisc ℚ(√NT) = 4·NT = 8` (`2 ≡ 2 mod 4`).

`E₇` sharpens the earlier obstruction precisely.  `two_not_a_discriminant`
showed the *naive* value `NT = 2` is not a matrix discriminant; but the
field's *fundamental* discriminant `8` **is** one (`8 = 2² − 4·(−1)`) —
just not `disc P`, which only ever yields `5`.  So `E₇` is field-realised
but `P`-excluded at every reading, while `E₈`'s `5` is the one number the
`P`-engine itself produces.
-/

namespace E213.Lib.Math.CayleyDickson.Tower.QuadraticFieldDiscriminant

open E213.Lib.Physics.Simplex.Counts
open E213.Lib.Math.CayleyDickson.Tower.TypeOOctahedral
open E213.Lib.Math.CayleyDickson.Tower.TypeEIcosian
open E213.Lib.Math.CayleyDickson.Tower.ExceptionalTraceSeed
open E213.Lib.Math.CayleyDickson.Tower.DiscForcingObstruction

/-- Fundamental discriminant of `ℚ(√m)` for squarefree `m`:
    `m` if `m ≡ 1 (mod 4)`, else `4m`. -/
def fundDisc (m : Int) : Int := if m % 4 == 1 then m else 4 * m

/-- The three seed fields' fundamental discriminants:
    `ℚ(√5) → 5`, `ℚ(√2) → 8`, `ℚ(√−3) → −3`. -/
theorem seed_field_discriminants :
    fundDisc 5 = 5 ∧ fundDisc 2 = 8 ∧ fundDisc (-3) = -3 := by decide

/-- **`E₈` double anchor — `disc P = fundDisc ℚ(√5) = NS+NT`.**  The
    matrix discriminant of the Möbius `P` and the number-field
    discriminant of `ℚ(√5)` are the *same* number `5 = NS+NT`. -/
theorem E8_disc_eq_field_disc :
    ((3 : Int) ^ 2 - 4 * 1 = (NS : Int) + NT)        -- 2D matrix scale: disc P
    ∧ (fundDisc ((NS : Int) + NT) = (NS : Int) + NT) -- number-field scale: fundDisc ℚ(√5)
    := by decide

/-- **`E₇` field discriminant — `fundDisc ℚ(√NT) = 4·NT = 8`**, and it
    *is* a matrix discriminant (`8 = 2² − 4·(−1)`), unlike the naive seed
    `NT = 2` (`two_not_a_discriminant`).  So `ℚ(√2)` is realisable; only
    its `P`-forcing fails (P yields `5`, never `8`). -/
theorem E7_field_disc :
    (fundDisc (NT : Int) = 4 * NT)                 -- fundDisc ℚ(√2) = 8
    ∧ ((2 : Int) ^ 2 - 4 * (-1) = 4 * (NT : Int))  -- 8 is a discriminant
    ∧ (∀ t d : Int, t * t - 4 * d ≠ (NT : Int))    -- but the naive seed 2 is not
    := ⟨by decide, by decide, two_not_a_discriminant⟩

/-- `E₆` field discriminant — `fundDisc ℚ(√(−NS)) = −NS = −3` (Eisenstein,
    the order-`3`/`6` discriminant). -/
theorem E6_field_disc : fundDisc (-(NS : Int)) = -(NS : Int) := by decide

/-- ★★★ **Seed re-entry: `NS+NT` is its own operand at every scale.**
    The number `5 = NS+NT` is simultaneously the 2D matrix discriminant
    `disc P`, the number-field discriminant `fundDisc ℚ(√5)`, and the 4D
    quaternion trace seed `(2·trace(g₅)+1)²` — one residue fed back
    through three scales of the construction (`diag_self_applies` at the
    level of the seed number).  `E₆`/`E₇` land on `−NS`/`4·NT`. -/
theorem seed_reentry :
    -- E₈: the same number NS+NT at three scales.
    ((3 : Int) ^ 2 - 4 * 1 = (NS : Int) + NT)                       -- 2D matrix: disc P
    ∧ (fundDisc ((NS : Int) + NT) = (NS : Int) + NT)                -- field: fundDisc ℚ(√5)
    ∧ ((⟨2, 0⟩ * icosTrace g5 + ⟨1, 0⟩) * (⟨2, 0⟩ * icosTrace g5 + ⟨1, 0⟩)
        = (⟨((NS : Int) + NT), 0⟩ : ZPhi))                          -- 4D quaternion trace
    -- E₇: field disc 4·NT, trace² = NT, naive seed 2 not a disc.
    ∧ (fundDisc (NT : Int) = 4 * NT)
    ∧ (octaTrace g8 * octaTrace g8 = (⟨(NT : Int), 0⟩ : ZRt2))
    -- E₆: field disc −NS.
    ∧ (fundDisc (-(NS : Int)) = -(NS : Int)) :=
  ⟨by decide, by decide, icosian_trace_seed_eq_NS_NT,
   by decide, octahedral_trace_sq_eq_NT, by decide⟩

end E213.Lib.Math.CayleyDickson.Tower.QuadraticFieldDiscriminant
