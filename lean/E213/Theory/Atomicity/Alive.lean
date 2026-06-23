/-!
# Alive predicate: derived from Clause 4 recursive application

**Status**: this file's previous "postulated, not
derived" framing has been **superseded** by the structural
derivation in `Theory/Atomicity/AliveDerivation.lean` (research
note ).

## Derivation summary

The "alive" predicate (both atom-multiplicities odd) is **derived**
from Clause 4 of the 213 axiom (`seed/AXIOM/02_axiom.md` §2.2 #4:
no self-pair `x/x`) **applied recursively at the count-Lens group
level**.

User insight:
  > "Raw is not in tree form.  Because every Raw is both an operation and
  >  an object — that is, operation and object are not even defined to begin with."
  > "The relation between objects would also be an object.  The type would also be an object."

If every Raw event is simultaneously operation and object, Clause 4
is not restricted to atomic Raw distinguishables — it applies at
every granularity, including **groups of Raw viewed as objects**.

For decomposition `n = 2a + 3b`: if `a` is even, the a binary-pair
atoms can themselves be grouped into a/2 pair-of-pairs — a Clause-4
violation at the binary group level.  So `a` must be odd; similarly
for `b`.

The "both odd" alive predicate is therefore the **count-Lens readout
of recursive Clause 4**, not a separate postulate.

## Lean bridge

  · `AliveDerivation.IsSelfPaired n := ∃ k, n = 2 * k` —
    binary group-level self-pair structure (Clause 4 forbidden)
  · `AliveDerivation.IsClause4Alive (a b) := ¬IsSelfPaired a ∧ ¬IsSelfPaired b`
  · `AliveDerivation.alive_iff_clause4_alive : IsAlive a b ↔ IsClause4Alive a b`
    — the formal dissolution (PURE)

This file retains the arithmetic surface-form of `Survives`/`Alive`
for compatibility with `Five.lean`, but the postulate-status caveat
is lifted.

(Former versions also appealed to "Raw's rule `x ≠ y`" as a
distinctness source.  That appeal is retired; the actual derivation
goes through Clause 4 recursive application as documented above.)
-/

namespace E213.Theory.Atomicity.Alive
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

end E213.Theory.Atomicity.Alive