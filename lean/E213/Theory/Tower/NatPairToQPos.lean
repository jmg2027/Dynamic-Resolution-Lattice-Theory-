import E213.Theory.Nat213.Core

/-!
# Theory.Tower.NatPairToQPos — ℚ_+ via multiplicative quotient

Following G73, demonstrates that ℚ_+ has the **same syntactic form**
as ℤ at the `(Nat213 × Nat213)` level, differing only in the
quotient relation:

| Target | Quotient relation |
|---|---|
| ℤ    | additive: `(a, b) ~ (c, d) ⟺ a + d = b + c` |
| ℚ_+  | multiplicative: `(a, b) ~ (c, d) ⟺ a · d = b · c` |

Both project from `Nat213 × Nat213` (same syntactic container).
Only the AXIS-GENERATOR fold differs (G72: `-` vs `/`).

This file provides the multiplicative-quotient counterpart at the
notation level — concrete witnesses (no commutativity proof of
mul required for the demos shown).

All theorems ∅-axiom.
-/

namespace E213.Theory.Tower.NatPairToQPos

open E213.Theory.Nat213

/-- Pair of positive naturals representing a positive rational.
    Same syntactic form as `NPair` in `NatPairToInt.lean` (modulo
    the element type — Nat213 here vs Lean Nat there). -/
abbrev QPair : Type := Nat213 × Nat213

/-- Multiplicative-diagonal equivalence: `(a, b) ~ (c, d) ⟺
    a · d = b · c`.  This is the Q-quotient relation, parallel to
    the Z-quotient `a + d = b + c`.  The "comma" is the
    axis-generator (G72: `/` for ℚ_+). -/
def qpairEquiv (p q : QPair) : Prop :=
  Nat213.mul p.1 q.2 = Nat213.mul p.2 q.1

/-- The "1" of ℚ_+ as a pair: `(1, 1)` via mult-quotient. -/
def qOne : QPair := (Nat213.one, Nat213.one)

/-- The atomic embedding `n ↦ (n, 1)` representing ℕ_+ ⊂ ℚ_+. -/
def natToQPair (n : Nat213) : QPair := (n, Nat213.one)

/-- ★ `qOne` is self-equivalent.  Trivial reflexivity case. -/
theorem qOne_equiv_self : qpairEquiv qOne qOne := rfl

/-- ★ Two equivalent pairs representing the rational `2`:
    `(2, 1) ~ (4, 2)` since `2 · 2 = 1 · 4 = 4`. -/
theorem two_pair_equiv :
    qpairEquiv (Nat213.two, Nat213.one) (Nat213.four, Nat213.two) := rfl

/-- ★ The natural embedding sends 1 to qOne. -/
theorem natToQPair_one : natToQPair Nat213.one = qOne := rfl

/-- ★★★ SYNTACTIC IDENTITY WITH ℤ: both ℤ and ℚ_+ pairs are
    Nat213-pair-shaped.  The structural notation `((a), (b))` is
    SHARED — only the quotient relation (axis-generator fold)
    differs.  This is G73's "Int213이랑 똑같이 생겼잖어". -/
theorem qpair_is_nat_pair_shaped :
    QPair = (Nat213 × Nat213) := rfl

end E213.Theory.Tower.NatPairToQPos
