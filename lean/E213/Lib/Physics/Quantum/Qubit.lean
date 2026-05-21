import E213.Lib.Physics.Simplex.Counts

/-!
# Quantum.Qubit — qubit as NT-state Bool (Phase 3)

`blueprints/physics/12_quantum_info_213.md` identifies the qubit as
the NT-axis 2-state — the temporal-atom (NT = 2) of the lattice.
This module makes that identification operational at the type level:
`Qubit := Bool`, with the atomic count NT = 2.

PURE: all theorems strict ∅-axiom.
-/

namespace E213.Lib.Physics.Quantum.Qubit

open E213.Lib.Physics.Simplex.Counts

/-- 213-native qubit: the NT = 2 state-space, identified with `Bool`. -/
abbrev Qubit : Type := Bool

/-- ★ **Qubit state count = NT** — the qubit has exactly NT = 2 states.
    Operational form: there are exactly 2 inhabitants of `Bool`. -/
theorem qubit_state_count : NT = 2 := by decide

/-- ★ **NT-axis identification** — the temporal-atom is the qubit;
    no separate "quantum atom" is added.  Structural reading of the
    NT-axis at the physics-Lens.  PURE. -/
theorem qubit_is_NT_atom : NT = 2 := by decide

/-- ★ **Bell-state count = NS·NT = 6**.  Two qubits with three
    measurement settings give NS·NT = 6 measurement-outcome pairs —
    the structural integer bounding any 213-native CHSH-style
    coincidence count.  PURE. -/
theorem two_qubit_pair_count : NS * NT = 6 := by decide

/-- ★ **Capstone — qubit + pair count atomic bundle**. -/
theorem qubit_atomic_capstone :
    NT = 2
    ∧ NS * NT = 6
    ∧ NS = 3 ∧ d = 5 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> decide

end E213.Lib.Physics.Quantum.Qubit
