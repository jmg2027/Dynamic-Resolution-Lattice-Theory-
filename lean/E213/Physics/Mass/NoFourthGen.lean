import E213.Physics.Substrate
import E213.Physics.Simplex.Generations
import E213.Physics.Simplex.Counts

/-!
# Phase 3 NoFourthGen — N_gen = 3 sharp falsifier

**Layer: App** (Phase 3 reformulation of Phase 1 Generations.lean).

Phase 1 `Generations.lean` derives N_gen = 3 + "no 4th gen
slot".  This file sharpens it into *falsifiable proposition form*.

## Integer prediction

  N_gen = C(NS, NT) = C(3, 2) = 3

C(NS, NT+1) = C(3, 3) = 1, already filled by 3 generations →
the *slot itself does not exist* for a 4th lepton/quark generation.

## Measurement status (2026)

  - LEP (Z width): N_ν = 2.984 ± 0.008 (exactly 3)
  - CMB (N_eff): 3.046 (3 light + radiation)
  - LHC: excluded region for 4th gen quark mass > 1 TeV expanding

DRLT gives N_gen = 3 *without exception*.  *Discovery of 4th generation
particle at any collider → 213 immediately discarded*.
-/

namespace E213.Physics.Mass.NoFourthGen

open E213.Physics.Simplex.Generations
open E213.Physics.Simplex.Counts

/-- Phase 3 sharp form: N_gen = 3 exactly. -/
theorem n_gen_sharp : N_gen = 3 := n_gen_eq_three

/-- No 4th gen slot (NS=3 → C(3,4)=0). -/
theorem no_fourth_slot : binom NS 4 = 0 := no_4th_gen_slot

/-- 5th, 6th gen also 0. -/
theorem no_fifth_slot : binom NS 5 = 0 := by decide
theorem no_sixth_slot : binom NS 6 = 0 := by decide

/-- ★ Falsifier formal ★
    DRLT gives N_gen = 3 exactly.  Discovery of 4th generation lepton or quark
    at any collider → contrapositive of this theorem → 213 discarded. -/
theorem fourth_gen_falsifier :
    -- N_gen exact
    (N_gen = 3)
    -- 4th, 5th, 6th all have no slot
    ∧ (binom NS 4 = 0)
    ∧ (binom NS 5 = 0)
    ∧ (binom NS 6 = 0)
    -- forced by C(NS, NT)
    ∧ (binom NS NT = 3) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  all_goals decide

end E213.Physics.Mass.NoFourthGen
