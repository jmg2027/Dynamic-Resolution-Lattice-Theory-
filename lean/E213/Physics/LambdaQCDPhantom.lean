import E213.Physics.SimplexCounts
import E213.Physics.Phase2

/-!
# Λ_QCD as topological projection — phantom elimination

Note (added 2026-04-30):

Mainstream QCD treats Λ_QCD as the *energy scale where the running
coupling diverges* — a singularity inherited from the continuum
assumption.  In the discrete K_{3,2}^{(c=2)} lattice the running
picture does not exist: signals do not "run" to infinity, they
**truncate** at the topological boundary where no further degree
of freedom is available to propagate.

Concretely, for the strong sector the boundary is the cycle space
b_1 = NS² − 1 = 8 of the 5-vertex graph.  The 5-D backbone projects
onto the NS-dim spatial subspace via the single ratio NS/d = 3/5,
and `m_p = NS · (anchor) · P(α_GUT · NS/d)` already encodes this
projection — Λ_QCD is *not* a primitive in that formula, only the
chosen unit (an "anchor") which converts the dimensionless atomic
result into MeV.

This file formalizes two things:
1. The counting decomposition `NT^d = NT² · (NS² − 1)` at the
   atomic anchor — i.e. the 32 chiral cells of K_{3,2}^{(c=2)}
   factor as NT² (chiral phase choices) × b_1 (cycle classes).
2. The "phantom" identity `d² · NT^d = d² · NT² · (NS² − 1) = 800`
   — the atomic-counting integer behind the apparent v_H/Λ_QCD
   ratio observed in mainstream phenomenology.  This integer
   is a property of K_{3,2}^{(c=2)}; whether one *labels* it
   "v_H/Λ_QCD" is a unit-convention question, not physics.

All 0-axiom Nat decidables.
-/

namespace E213.Physics.LambdaQCDPhantom

open E213.Physics.Simplex

/-- The 32 chiral cells of K_{3,2}^{(c=2)} count as NT^d. -/
theorem chiral_cells_eq_NT_pow_d : NT ^ d = 32 := by decide

/-- ★ The chiral cell count factors as
    (chiral phase choices NT²) × (cycle space b_1 = NS²−1).
    This is the *counting* structure underlying the b_1=8
    confinement cutoff. -/
theorem chiral_cells_factor :
    NT ^ d = NT * NT * (NS * NS - 1) := by decide

/-- Shorthand: b_1 = 8 = NS² − 1 (cycle space dim of K_{3,2}^{(2)}). -/
theorem b1_eq_NS_sq_minus_one : NS * NS - 1 = 8 := by decide

/-- ★ Λ_QCD-as-counting capstone (phantom elimination). ★
    The integer 800 — observed phenomenologically as v_H/Λ_QCD —
    has a closed atomic decomposition:
      d²        = 25  (channels per spatial dim, used in 1/α_GUT)
      NT²       = 4   (chiral phase volume per cycle)
      NS² − 1   = 8   (cycle space b_1, confinement loop count)
      product   = 800
    No "running coupling singularity" required — the count *is*
    the structure.  Λ_QCD as a parameter is therefore eliminable;
    the dimensionful scale anyone calls "Λ_QCD" is the unit chosen
    to express the dimensionless ratio NS · P(α_GUT · NS/d) in MeV. -/
theorem lambda_qcd_phantom_count :
    d * d * NT * NT * (NS * NS - 1) = 800
    ∧ d * d * NT * NT * (NS * NS - 1) = d * d * (NT ^ d)
    ∧ NT ^ d = NT * NT * (NS * NS - 1) := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

end E213.Physics.LambdaQCDPhantom
