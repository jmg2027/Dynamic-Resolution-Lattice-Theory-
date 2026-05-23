import E213.Lens.Number.Nat213.Peano

/-!
# Lens.Number.Nat213.Tower.NatPairToQPos — ℚ_+ via multiplicative quotient

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

namespace E213.Lens.Number.Nat213.Tower.NatPairToQPos

open E213.Lens.Number.Nat213.Peano

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
    differs.  This is G73's "looks identical to Int213". -/
theorem qpair_is_nat_pair_shaped :
    QPair = (Nat213 × Nat213) := rfl

/-! ### qpairEquiv: equivalence relation properties (, iteration #22)

`qpairEquiv` is reflexive and symmetric — using only `Nat213.mul_comm`
from the new Peano semiring law set.  (Transitivity also holds but
its proof requires multiplicative cancellation, which we have via
`mul_left_cancel` — added separately.) -/

open E213.Lens.Number.Nat213.Peano (Nat213)

/-- **Reflexivity** of `qpairEquiv`: `mul p.1 p.2 = mul p.2 p.1`
    by `mul_comm`. -/
theorem qpairEquiv_refl (p : QPair) : qpairEquiv p p := by
  show Nat213.mul p.1 p.2 = Nat213.mul p.2 p.1
  exact Nat213.mul_comm p.1 p.2

/-- **Symmetry** of `qpairEquiv`: bidirectional `mul_comm` rewrite. -/
theorem qpairEquiv_symm {p q : QPair} (h : qpairEquiv p q) :
    qpairEquiv q p := by
  show Nat213.mul q.1 p.2 = Nat213.mul q.2 p.1
  rw [Nat213.mul_comm q.1 p.2, Nat213.mul_comm q.2 p.1]
  exact h.symm

/-- **Transitivity** of `qpairEquiv`: closes the equivalence-relation
    proof.  Uses `mul_right_cancel` (Peano iteration #6) to drop
    the common factor `q.2` after substituting `h1`, `h2`.

    Standard QPair Grothendieck-completion lemma: cross-multiply the
    two hypotheses, substitute, cancel. -/
theorem qpairEquiv_trans {p q r : QPair}
    (h1 : qpairEquiv p q) (h2 : qpairEquiv q r) :
    qpairEquiv p r := by
  show Nat213.mul p.1 r.2 = Nat213.mul p.2 r.1
  apply Nat213.mul_right_cancel (c := q.2)
  show Nat213.mul (Nat213.mul p.1 r.2) q.2 = Nat213.mul (Nat213.mul p.2 r.1) q.2
  rw [Nat213.mul_assoc p.1 r.2 q.2,
      Nat213.mul_comm r.2 q.2,
      ← Nat213.mul_assoc p.1 q.2 r.2]
  rw [h1]
  rw [Nat213.mul_assoc p.2 q.1 r.2, h2]
  rw [Nat213.mul_comm q.2 r.1, ← Nat213.mul_assoc p.2 r.1 q.2]

end E213.Lens.Number.Nat213.Tower.NatPairToQPos
