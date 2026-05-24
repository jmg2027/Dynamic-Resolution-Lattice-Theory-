import E213.Lib.Math.Cohomology.Bipartite.V33OppositeCup

/-!
# Cup descent to cohomology at K_{3,3}^{(c=2)}

The chain-level computation in `V33OppositeCup` showed
`g1 ⌣ g4 = (1, 1, 0, 1, 1, 0, 0, 0, 0)` — non-zero at 4 of 9
faces.  This file verifies that the cohomology class
`[g1 ⌣ g4] ∈ H²` is nevertheless **zero**, via an explicit
cobounding chain `σ = e_2 + e_4`.

## Why this matters

If `[g1 ⌣ g4] = 0` in H² (despite chain-level non-vanishing),
then the cup table on H¹ × H¹ → H² may still be **forced to
vanish** at K_{3,3}^{(c=2)} just as at K_{3,2}^{(c=2)} — meaning
the Massey detection mechanism transfers.

This is the analogue of the "cup-descent" phenomenon at
K_{3,2}^{(c=2)}: chain-level cup can be non-zero but always
lands in `im δ¹`, so cohomology cup vanishes.

## The cobounding chain

`σ := e_2 + e_4 ∈ C¹` satisfies `δ¹σ = (1, 1, 0, 1, 1, 0, 0, 0, 0)
= g1 ⌣ g4` (verified by `decide`).

  · δ¹(e_2) = (1, 0, 1, 1, 0, 1, 0, 0, 0) (faces containing e_2)
  · δ¹(e_4) = (0, 1, 1, 0, 1, 1, 0, 0, 0) (faces containing e_4)
  · δ¹(e_2 + e_4) = (1, 1, 0, 1, 1, 0, 0, 0, 0) ✓

STRICT ∅-AXIOM.
-/

namespace E213.Lib.Math.Cohomology.Bipartite.V33CupDescent

open E213.Lib.Math.Cohomology.Bipartite.V33 (CochE delta1)
open E213.Lib.Math.Cohomology.Bipartite.V33OppositeCup (cupOpp g1 g4)

/-- Cobounding chain σ = e_2 + e_4. -/
def sigma : CochE := fun e => decide (e.val = 2 ∨ e.val = 4)

/-- δ¹(σ) at face f, evaluated. -/
theorem delta1_sigma_face_values :
    delta1 sigma ⟨0, by decide⟩ = true
    ∧ delta1 sigma ⟨1, by decide⟩ = true
    ∧ delta1 sigma ⟨2, by decide⟩ = false
    ∧ delta1 sigma ⟨3, by decide⟩ = true
    ∧ delta1 sigma ⟨4, by decide⟩ = true
    ∧ delta1 sigma ⟨5, by decide⟩ = false
    ∧ delta1 sigma ⟨6, by decide⟩ = false
    ∧ delta1 sigma ⟨7, by decide⟩ = false
    ∧ delta1 sigma ⟨8, by decide⟩ = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- ★ **g1 ⌣ g4 cobounds at K_{3,3}^{(c=2)}**: the chain-level
    non-trivial cup `(1, 1, 0, 1, 1, 0, 0, 0, 0)` equals
    `δ¹(e_2 + e_4)`, so `[g1 ⌣ g4] = 0 ∈ H²`.  Bundled
    per-face form. -/
theorem cup_g1_g4_descends_to_zero_bundled :
    cupOpp g1 g4 ⟨0, by decide⟩ = delta1 sigma ⟨0, by decide⟩
    ∧ cupOpp g1 g4 ⟨1, by decide⟩ = delta1 sigma ⟨1, by decide⟩
    ∧ cupOpp g1 g4 ⟨2, by decide⟩ = delta1 sigma ⟨2, by decide⟩
    ∧ cupOpp g1 g4 ⟨3, by decide⟩ = delta1 sigma ⟨3, by decide⟩
    ∧ cupOpp g1 g4 ⟨4, by decide⟩ = delta1 sigma ⟨4, by decide⟩
    ∧ cupOpp g1 g4 ⟨5, by decide⟩ = delta1 sigma ⟨5, by decide⟩
    ∧ cupOpp g1 g4 ⟨6, by decide⟩ = delta1 sigma ⟨6, by decide⟩
    ∧ cupOpp g1 g4 ⟨7, by decide⟩ = delta1 sigma ⟨7, by decide⟩
    ∧ cupOpp g1 g4 ⟨8, by decide⟩ = delta1 sigma ⟨8, by decide⟩ := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-! ## §1 — Massey-detection-transfer conjecture

Hypothesis (preliminary based on K_{3,2} pattern + g1 ⌣ g4
witness): at K_{3,3}^{(c=2)} the cup table on H¹ × H¹ → H² is
forced to vanish, with cup-descent holding for every basis pair.
If so, non-vacuous Massey at K_{3,3}^{(c=2)} would require
secondary operations analogous to K_{3,2}^{(c=2)}.

This file verifies the descent for one specific star × incidence
pair (g1, g4).  A full cup-descent theorem would verify it for
all 6 × 6 = 36 basis pairs.  Deferred. -/

end E213.Lib.Math.Cohomology.Bipartite.V33CupDescent
