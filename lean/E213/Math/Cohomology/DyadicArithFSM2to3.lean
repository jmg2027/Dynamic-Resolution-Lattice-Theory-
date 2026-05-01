import E213.Math.Cohomology.DyadicArithFSM3

/-!
# ArithFSM2 ⊂ ArithFSM3 — padding inclusion

Every 2-state arithmetic FSM can be embedded into a 3-state one
by adding an inert third component.  Inclusion is bit-stream-faithful.
-/

namespace E213.Math.Cohomology.DyadicConjecture

/-- Pad ArithFSM2(n) into ArithFSM3(n) by adding an inert
    third component.  init = (a, b, 0), step ignores it. -/
def ArithFSM2.padTo3 {n : Nat} (hn : 0 < n) (m : ArithFSM2 n) : ArithFSM3 n where
  init := (m.init.1, m.init.2, ⟨0, hn⟩)
  step p := let (a, b, _) := p
    let (a', b') := m.step (a, b)
    (a', b', ⟨0, hn⟩)
  out p := m.out (p.1, p.2.1)

/-- Padding via padTo3 preserves the bit stream's run components. -/
theorem padTo3_run_components {n : Nat} (hn : 0 < n) (m : ArithFSM2 n) (k : Nat) :
    ((m.padTo3 hn).run k).1 = (m.run k).1
    ∧ ((m.padTo3 hn).run k).2.1 = (m.run k).2 := by
  induction k with
  | zero => exact ⟨rfl, rfl⟩
  | succ k' ih =>
    obtain ⟨ih1, ih2⟩ := ih
    have hpair : ((m.padTo3 hn).run k').1 = (m.run k').1 ∧
                 ((m.padTo3 hn).run k').2.1 = (m.run k').2 := ⟨ih1, ih2⟩
    show ((m.padTo3 hn).step ((m.padTo3 hn).run k')).1 = (m.step (m.run k')).1
       ∧ ((m.padTo3 hn).step ((m.padTo3 hn).run k')).2.1 = (m.step (m.run k')).2
    have hrun : ((m.padTo3 hn).run k').1 = (m.run k').1 := ih1
    have hrun2 : ((m.padTo3 hn).run k').2.1 = (m.run k').2 := ih2
    refine ⟨?_, ?_⟩
    · show (m.step (((m.padTo3 hn).run k').1, ((m.padTo3 hn).run k').2.1)).1
            = (m.step (m.run k')).1
      rw [hrun, hrun2]
    · show (m.step (((m.padTo3 hn).run k').1, ((m.padTo3 hn).run k').2.1)).2
            = (m.step (m.run k')).2
      rw [hrun, hrun2]

/-- ★★★★ padTo3 preserves the bit stream. -/
theorem padTo3_bits_eq {n : Nat} (hn : 0 < n) (m : ArithFSM2 n) (k : Nat) :
    (m.padTo3 hn).bits k = m.bits k := by
  show m.out (((m.padTo3 hn).run k).1, ((m.padTo3 hn).run k).2.1)
      = m.out (m.run k)
  rw [(padTo3_run_components hn m k).1, (padTo3_run_components hn m k).2]

end E213.Math.Cohomology.DyadicConjecture
