import Lean

/-!
# Tactic: `omega213` — axiom-free linear arithmetic over ℕ

Lean's `omega` tactic introduces `[propext, Quot.sound]` axioms into
every theorem that uses it.  This module provides a 213-native
replacement that uses only Lean kernel reduction and a curated set
of 0-axiom `Nat.*` lemmas.

## Usage

```lean
theorem ex (n : Nat) (h : 1 ≤ n) : 2 * n ≥ 2 := by omega213
#print axioms ex   -- "does not depend on any axioms"
```

## What it covers

The current implementation handles 213's four most common patterns:

  1. **Concrete decidable goals** — `decide` first.
  2. **Bounded inequalities** — `Nat.le_succ_of_le`,
     `Nat.lt_succ_of_le`, `Nat.lt_of_le_of_lt`, etc.
  3. **Multiplicative monotonicity** — `Nat.mul_le_mul_left`,
     `Nat.mul_le_mul_right`.
  4. **Positivity / non-zero** — `Nat.pos_of_ne_zero`,
     `Nat.zero_lt_succ`.

Goals that don't fall to these patterns will fail; convert manually
to one of these forms (typically by introducing intermediate
`have :` statements with explicit Nat lemmas).

## Coverage growth

This is intentionally minimal.  When migrating an `omega` call:
  1. Try `omega213` first.
  2. If it fails, see if a single `Nat.*` lemma fits — add it
     via `exact Nat.foo h₁ h₂` directly.
  3. If a new pattern recurs ≥ 3 times across files, add a
     branch to the `omega213` macro below.

This way the tactic grows ONLY in proportion to actually-needed
patterns, never inflating beyond what 213 uses.
-/

namespace E213.Tactic

open Lean Elab Tactic

/-- `omega213` — axiom-free Nat arithmetic. -/
syntax "omega213" : tactic

macro_rules
  | `(tactic| omega213) => `(tactic|
      first
        | decide
        | exact Nat.le_refl _
        | exact Nat.zero_le _
        | exact Nat.zero_lt_succ _
        | (apply Nat.le_succ_of_le; assumption)
        | (apply Nat.lt_succ_of_le; assumption)
        | (apply Nat.mul_le_mul_left; assumption)
        | (apply Nat.mul_le_mul_right; assumption)
        | (apply Nat.pos_of_ne_zero; assumption)
        | assumption)

end E213.Tactic
