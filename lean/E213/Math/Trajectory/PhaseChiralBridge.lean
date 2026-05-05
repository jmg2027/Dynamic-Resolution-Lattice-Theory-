import E213.Kernel.Tactic.Mod213
import E213.Physics.Simplex.Counts

/-!
# Math.Trajectory.PhaseChiralBridge

Formal bridge between the two ∅-axiom decompositions of the
K_{3,2}^{(2)} skeleton (atomic shape (NS, NT, d) = (3, 2, 5)):

  - **View A (, cyclotomic)**:
    `mod6 n ↔ (parity n, mod3 n)` — CRT
    ℤ/6 ≅ ℤ/2 × ℤ/3, the Eisenstein 6th-roots-of-unity walk.
    Lives in `Kernel/Tactic/Mod213.lean`.

  - **View B (chiral split, vertex-count)**:
    `NS + NT = d`  —  Vec 5 = VecS ⊕ VecT, direct sum.
    Lives in `Physics/Simplex/Counts.lean` (and lifted to
    Hilbert space in `Math/Linalg213/Chiral.lean`).

Both views agree on the same 5-vertex graph.  They co-exist
*because* atomicity forces (NS, NT, d) = (3, 2, 5) — see
`research-notes/G4_chiral_phase_duality.md` for the principle.

This file is the canonical import site for any future "d = 5"
theorem that needs either view, ensuring the two foundational
decompositions are pulled in together.
-/

namespace E213.Math.Trajectory.PhaseChiralBridge

open E213.Tactic.Mod213
open E213.Physics.Simplex.Counts

/-! ### View B — chiral vertex-count split -/

/-- Chiral count: the 5-vertex skeleton splits as NS + NT spatial +
    temporal vertices.  ∅-axiom by `decide` on concrete constants. -/
theorem chiral_count : NS + NT = d := by decide

/-! ### View A — CRT decomposition

These restate `Mod213.mod6_parity` / `Mod213.mod6_mod3` at this
canonical bridge site, giving downstream files a single import. -/

/-- CRT half 1: parity (mod 2 component) of mod6 walk equals parity
    of n.  ∅-axiom (re-export). -/
theorem phase_parity (n : Nat) : parity (mod6 n) = parity n :=
  mod6_parity n

/-- CRT half 2: mod3 (mod 3 component) of mod6 walk equals mod3 of
    n.  ∅-axiom (re-export). -/
theorem phase_mod3 (n : Nat) : mod3 (mod6 n) = mod3 n :=
  mod6_mod3 n

/-! ### Bridge — both views, packaged together -/

/-- **Atomic-five duality capstone**: the same K_{3,2}^{(2)} skeleton
    supports BOTH the chiral vertex-count split (NS + NT = d) AND
    the CRT phase-walk decomposition (mod6 ↔ (parity, mod3)).
    Both views are ∅-axiom; their co-existence is forced by
    atomicity (3, 2, 5).  Import this capstone as the canonical
    bridge for any "d = 5" reasoning that uses either view. -/
theorem atomic_five_dual :
    NS + NT = d
    ∧ (∀ n, parity (mod6 n) = parity n ∧ mod3 (mod6 n) = mod3 n) :=
  ⟨chiral_count, fun n => ⟨phase_parity n, phase_mod3 n⟩⟩

/-! ### Chiral pair — combined (parity, mod3) read of an `n`

`chiralPair n = (parity n, mod3 n)` is the canonical *combined*
View-A coordinate of `n`.  By CRT it is in bijection with `mod6 n`
on the range 0..5; the table makes the bijection explicit. -/

/-- Chiral pair: the canonical (View A) decomposition. -/
def chiralPair (n : Nat) : Bool × Nat := (parity n, mod3 n)

/-- `chiralPair (mod6 n) = chiralPair n` — CRT in compact form. -/
theorem chiralPair_mod6 (n : Nat) : chiralPair (mod6 n) = chiralPair n := by
  unfold chiralPair
  rw [phase_parity, phase_mod3]

/-- The 6 distinct chiral pairs of `mod6 ∈ {0..5}`.  Concrete
    enumeration witnesses the bijection ℤ/6 ↔ ℤ/2 × ℤ/3. -/
theorem chiralPair_table :
    chiralPair 0 = (false, 0) ∧ chiralPair 1 = (true, 1)
    ∧ chiralPair 2 = (false, 2) ∧ chiralPair 3 = (true, 0)
    ∧ chiralPair 4 = (false, 1) ∧ chiralPair 5 = (true, 2) :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

end E213.Math.Trajectory.PhaseChiralBridge
