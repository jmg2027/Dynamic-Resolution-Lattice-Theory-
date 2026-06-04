import E213.Lens.Number.Nat213.Tower.NatPairToInt
import E213.Lib.Math.Algebra.Mobius213OneAsGlue
import E213.Lib.Math.Analysis.Cauchy.EllipticPeriodicTier

/-!
# The founding invert-move is the elliptic floor of the discriminant dial

Two marathons met at one structure.  The **number-tower founding** built each rung of `ℕ → ℤ →
ℚ → ℝ` as a *static* pair-completion: the inverse-realising **swap** `(a,b) ↦ (b,a)`, which the
projection reads as **negation** (`NatPairToInt.swap_realizes_negation`), period-2 because `NT = 2`
(`PairCompletion.swap_order_eq_NT`), fixed only at the residue's `0`
(`zero_unique_negation_fixed`), and the shared unit `1 = NS − NT = det P`
(`SharedUnitAcrossReadings`).  The **non-holonomicity / discriminant dial** set that same pair-move
in *motion* as a recurrence: the order-2 companion `comp p q`, its discriminant `p² − 4q` reading off
the holonomicity tier (`EllipticPeriodicTier`).

This file pins the meeting point ∅-axiom: the **elliptic floor** of the dial — the unimodular
`comp 0 1 = S` — *is* the founding swap-move read dynamically.  Its determinant is the founding unit
`NS − NT = 1`; it is elliptic (`disc < 0`); its central element `S² = −I` is negation-of-identity —
the same negation the founding swap realises, the same period-2 (`NT`) involution fixed only at `0`.
So the static "invert is one move" and the dynamic discriminant floor are one structure: the number
tower completes the pair once; the dial iterates the same move, the elliptic floor being the
iteration that stays the pure period-2 swap.
-/

namespace E213.Lens.Number.FoundingDynamicBridge

open E213.Lib.Math.Analysis.Cauchy.EllipticPeriodicTier (comp comp_eq_S comp_det comp_disc)
open E213.Lib.Math.NumberSystems.Real213.HyperbolicEllipticTrace (Mat2)
open E213.Lens.Number.Nat213.Tower.NatPairToInt (npairToInt swap_realizes_negation
  zero_unique_negation_fixed)

/-- ★★★★ **The founding invert-swap is the elliptic floor of the discriminant dial.**  Six facts,
    three from each marathon, that are one structure:

      1. the dial's elliptic floor companion `comp 0 1` *is* the elliptic generator `S`;
      2. its determinant is the founding shared unit `NS − NT = 1` (the static count-difference glue);
      3. it is elliptic — `disc < 0` (the π/rotation face);
      4. its central element `S² = −I` is negation-of-identity (the dynamic step is negation);
      5. the founding pair-swap realises exactly that negation (`swap`-read = `−`);
      6. negation is fixed only at the residue's `0` — the additive center both readings share.

    Static pair-completion (founding) and dynamic pair-iteration (dial) meet at the period-2
    swap. -/
theorem founding_swap_is_elliptic_floor :
    comp 0 1 = Mat2.S
    ∧ Mat2.det (comp 0 1) = (E213.Lib.Physics.Simplex.Counts.NS : Int)
        - E213.Lib.Physics.Simplex.Counts.NT
    ∧ Mat2.disc (comp 0 1) < 0
    ∧ Mat2.S * Mat2.S = Mat2.negI
    ∧ npairToInt (0, 5) = -(npairToInt (5, 0))
    ∧ (∀ z : Int, -z = z ↔ z = 0) := by
  refine ⟨comp_eq_S, ?_, ?_, ?_, ?_, zero_unique_negation_fixed⟩
  · rw [comp_det]; decide
  · rw [comp_disc]; decide
  · decide
  · exact (swap_realizes_negation).2.2

end E213.Lens.Number.FoundingDynamicBridge
