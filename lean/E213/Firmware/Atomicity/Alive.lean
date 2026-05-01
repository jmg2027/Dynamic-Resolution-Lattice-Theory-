/-!
# Alive predicate: a structural principle (not derived from Raw alone)

**Honest framing.** The "alive" predicate of §6 (both atom-multiplicities
odd) is *not* a consequence of the axiom "there exists a relation object
between two objects." The axiom supplies Raw (§1) and the swap
automorphism (§3) — nothing more.

The *Atomic* definition of §6 adds, as a **separate structural principle**,
antisymmetric multiplicity (paired structurally-identical copies cancel).
This is the exterior-algebra / fermion-statistics pattern. It is a
natural partner to Raw's 2-object, binary structure but is **postulated**,
not derived.

This file therefore only defines "Survives" arithmetically and states the
trivial equivalence with oddness. There is no bridge-theorem to Raw's
primitive constructors, because no such theorem is formally provable
from the axiom alone.

(Former versions of this file appealed to "Raw's rule `x ≠ y`" as a
distinctness source. Since the axiom provides no equality or
inequality primitive on objects, `x ≠ y` is no longer part of Raw's
inductive structure, and that appeal is retired.)
-/

namespace E213.Firmware.Atomicity.Alive
/-- Surviving residue of a multiplicity under the antisymmetry
    principle: each pair of structurally identical copies annihilates. -/
def residue (a : Nat) : Nat := a % 2

/-- A multiplicity *survives* iff its residue is 1 (odd). -/
def Survives (a : Nat) : Prop := residue a = 1

theorem survives_iff_odd (a : Nat) : Survives a ↔ a % 2 = 1 := by
  unfold Survives residue; rfl

/-- Both atom-types survive iff both multiplicities are odd. -/
def BothSurvive (a b : Nat) : Prop := Survives a ∧ Survives b

theorem alive_iff_odd_pair (a b : Nat) :
    BothSurvive a b ↔ a % 2 = 1 ∧ b % 2 = 1 := by
  unfold BothSurvive Survives residue; exact Iff.rfl

end E213.Firmware.Atomicity.Alive