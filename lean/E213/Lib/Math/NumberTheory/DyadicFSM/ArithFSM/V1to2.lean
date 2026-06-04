import E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM.V1
import E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM

/-!
# ArithFSM₁ ⊂ ArithFSM₂ — padding inclusion (degree 1 ↪ degree 2)

Every 1-state arithmetic FSM embeds into a 2-state one by adding
an inert second component.  Bit-stream-faithful by construction.

Combined with `ArithFSM2.padTo3` (already proven), this completes
the lower portion of the algebraic-degree tower:

  ArithFSM₁ ⊂ ArithFSM₂ ⊂ ArithFSM₃ ⊂ ...

Each inclusion preserves the bit stream, so the *minimal degree*
in which a stream appears = its 213-native algebraic degree.
-/

namespace E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM.V1

open E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM (ArithFSM2)

/-- Pad ArithFSM₁(n) into ArithFSM₂(n) by adding an inert
    second component.  init = (a, 0), step ignores it.

    Defined at the `ArithFSM1` namespace so that dot notation
    `m.padTo2 hn` resolves correctly (Lean's dot lookup walks the
    type's namespace, which is `…V1.ArithFSM1`, not the
    sibling `V1to2`). -/
def ArithFSM1.padTo2 {n : Nat} (hn : 0 < n) (m : ArithFSM1 n) : ArithFSM2 n where
  init := (m.init, ⟨0, hn⟩)
  step p := let (a, _) := p
    (m.step a, ⟨0, hn⟩)
  out p := m.out p.1

end E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM.V1

namespace E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM.V1to2

open E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM.V1 (ArithFSM1)
open E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM (ArithFSM2)

/-- ★★★ padTo2 preserves the run's first component. -/
theorem padTo2_run_components {n : Nat} (hn : 0 < n) (m : ArithFSM1 n) (k : Nat) :
    ((m.padTo2 hn).run k).1 = m.run k := by
  induction k with
  | zero => rfl
  | succ k' ih =>
    show ((m.padTo2 hn).step ((m.padTo2 hn).run k')).1 = m.step (m.run k')
    have h : ((m.padTo2 hn).run k').1 = m.run k' := ih
    show (m.step ((m.padTo2 hn).run k').1) = m.step (m.run k')
    rw [h]

/-- ★★★★ padTo2 preserves the bit stream. -/
theorem padTo2_bits_eq {n : Nat} (hn : 0 < n) (m : ArithFSM1 n) (k : Nat) :
    (m.padTo2 hn).bits k = m.bits k := by
  show m.out ((m.padTo2 hn).run k).1 = m.out (m.run k)
  rw [padTo2_run_components hn m k]

end E213.Lib.Math.NumberTheory.DyadicFSM.ArithFSM.V1to2
