import E213.Lib.Math.Combinatorics.Logic.Proof

/-!
# Logic — Cut elimination concrete witnesses (∅-axiom)

Closes the "skeleton" deferral in `Logic/Proof.lean`'s `normalize`
function.  The base file defined `normalize` and one rfl theorem
(`normalize_trivial`); this file proves substantive cut-elimination
properties at the *witness* level (concrete trajectories), all
∅-axiom.

213-native paradigm: cut-elimination = deciding a `List Bool` by
walking left-to-right, cancelling adjacent unequal pairs.  This is
Bool-decidable kernel-computable, so each fact below is `rfl`.
-/

namespace E213.Lib.Math.Combinatorics.Logic.CutElimination

open E213.Lib.Math.Combinatorics.Logic.Proof
  (Trajectory normalize compose proofLength)

/-- ★ Singleton trajectory: `normalize [true]` = `[true]` (rfl). -/
theorem normalize_singleton_true : normalize [true] = [true] := rfl

/-- ★ Singleton: `normalize [false]` = `[false]` (rfl). -/
theorem normalize_singleton_false : normalize [false] = [false] := rfl

/-- ★ Same-bit pair: `[true, true]` is preserved (no cancellation). -/
theorem normalize_tt : normalize [true, true] = [true, true] := rfl

/-- ★ Same-bit pair: `[false, false]` is preserved. -/
theorem normalize_ff : normalize [false, false] = [false, false] := rfl

/-- ★ **Cut-elimination atomic** ★ — `[true, false]` mutually
    cancels to the trivial proof. -/
theorem normalize_tf : normalize [true, false] = [] := rfl

/-- ★ **Cut-elimination atomic (other direction)** — `[false, true]`
    mutually cancels. -/
theorem normalize_ft : normalize [false, true] = [] := rfl

/-- ★ Triple cancellation: `[true, false, true]` → `[true]`
    (first pair cancels, residue `[true]` survives).  -/
theorem normalize_tft : normalize [true, false, true] = [true] := rfl

/-- ★ Quadruple cancellation: `[true, false, false, true]` → `[]`.
    First pair cancels (`a ≠ b`), recursion continues on the
    *remainder* `[false, true]`, which itself cancels.  Single-pass
    cut elimination eliminates fully here. -/
theorem normalize_tfft : normalize [true, false, false, true] = [] := rfl

/-- ★ Length is preserved or decreased by 2 per cancellation step
    — concrete witness on `[true, false]`. -/
theorem normalize_length_decrease :
    proofLength (normalize [true, false])
      = proofLength ([] : Trajectory) := rfl

/-- ★ Composition of a trivial proof with itself is trivial. -/
theorem compose_trivial_trivial :
    compose ([] : Trajectory) [] = [] := rfl

end E213.Lib.Math.Combinatorics.Logic.CutElimination
