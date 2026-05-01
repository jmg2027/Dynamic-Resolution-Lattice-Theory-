import E213.Math.Cohomology.DyadicArithFSM1
import E213.Math.Cohomology.DyadicArithFSM

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

namespace E213.Math.Cohomology.DyadicConjecture

/-- Pad ArithFSM₁(n) into ArithFSM₂(n) by adding an inert
    second component.  init = (a, 0), step ignores it. -/
def ArithFSM1.padTo2 {n : Nat} (hn : 0 < n) (m : ArithFSM1 n) : ArithFSM2 n where
  init := (m.init, ⟨0, hn⟩)
  step p := let (a, _) := p
    (m.step a, ⟨0, hn⟩)
  out p := m.out p.1

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

end E213.Math.Cohomology.DyadicConjecture
