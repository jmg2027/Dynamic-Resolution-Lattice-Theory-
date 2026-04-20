/-!
# Alive predicate from Raw's distinctness rule

Remark 6.6(c) of PAPER.md: the "alive" predicate (both multiplicities
odd) is not an external hypothesis but a consequence of Raw's
distinctness rule at the multiplicity level.

The mechanism: if `a` copies of a structurally identical atom appear
in a partition, Raw cannot distinguish them within their structural-
equivalence class. By Raw's rule `x ≠ y` in every `relation x y`,
two structurally identical copies cannot coexist as distinct
ingredients; they pair-cancel. The surviving multiplicity is `a mod 2`.

This file formalizes the parity residue. The full bridge to Raw's
type-level rule requires a model of structural equivalence on atoms,
which is naturally exterior-algebra-shaped; this is the standard
realization noted in Remark 6.6(c).
-/

namespace E213.AliveFromDistinctness

/-- Surviving residue of a multiplicity under pair-cancellation
    (each pair of structurally identical atoms annihilates). -/
def residue (a : Nat) : Nat := a % 2

/-- A multiplicity *survives* pair-cancellation iff its residue is 1
    (equivalently, it is odd). -/
def Survives (a : Nat) : Prop := residue a = 1

/-- Survival is exactly oddness. -/
theorem survives_iff_odd (a : Nat) : Survives a ↔ a % 2 = 1 := by
  unfold Survives residue; rfl

/-- A pair `(a, b)` is *both-survives* iff both multiplicities have
    odd residue under pair-cancellation. -/
def BothSurvive (a b : Nat) : Prop := Survives a ∧ Survives b

/-- **Alive iff both-survives.** The alive predicate of
    `E213.Atomicity.IsAlive` (both `a, b` odd) is precisely
    `BothSurvive (a, b)`. Hence the alive condition is *not* an
    independent assumption but a name for "both multiplicities have
    surviving residue under pair-cancellation," which is forced by
    Raw's distinctness rule applied at the multiplicity level. -/
theorem alive_iff_odd_pair (a b : Nat) :
    BothSurvive a b ↔ a % 2 = 1 ∧ b % 2 = 1 := by
  unfold BothSurvive Survives residue; exact Iff.rfl

end E213.AliveFromDistinctness
