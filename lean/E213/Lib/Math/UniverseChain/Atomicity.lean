import E213.Theory.Atomicity.Five

/-!
# Step 1 — Atomicity forces size 5 (∅-axiom)

The first link in the deductive chain.  Pure re-export wrapper
around `Theory.Atomicity.Five.atomic_iff_five` (already
∅-axiom).

## Statement

Given the atom set `{2, 3}`, define a number `n` to be **atomic**
if it admits exactly one *alive* decomposition `n = 2a + 3b`
(both `a, b` having parity = `true`).  Then:

    Atomic n  ⟺  n = 5.

I.e. atomicity *uniquely* selects the size 5.

This file does not introduce new content; it re-exports the
existing ∅-axiom proof under a chain-aligned namespace so that
later steps reference a single canonical entry.
-/

namespace E213.Lib.Math.UniverseChain.Atomicity

/-- Predicate: `n = 2a + 3b`. -/
abbrev Decomp (n a b : Nat) : Prop :=
  E213.Theory.Atomicity.Five.Decomp n a b

/-- Predicate: both decomposition coefficients are odd. -/
abbrev IsAlive (a b : Nat) : Prop :=
  E213.Theory.Atomicity.Five.IsAlive a b

/-- Atomic: unique alive decomposition. -/
abbrev Atomic (n : Nat) : Prop :=
  E213.Theory.Atomicity.Five.Atomic n

/-- ★ **Step 1**: atomicity ⇔ size = 5. -/
theorem atomic_iff_five (n : Nat) : Atomic n ↔ n = 5 :=
  E213.Theory.Atomicity.Five.atomic_iff_five n

/-- ★ Existence: 5 is atomic. -/
theorem five_is_atomic : Atomic 5 :=
  E213.Theory.Atomicity.Five.atomic_five

/-- ★ Forward direction: any atomic n is 5. -/
theorem atomic_implies_five (n : Nat) (h : Atomic n) : n = 5 :=
  E213.Theory.Atomicity.Five.atomic_implies_five n h

end E213.Lib.Math.UniverseChain.Atomicity
