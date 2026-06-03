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

/-! ### Reciprocal involution — the multiplicative twin of ℤ's negation

`NatPairToInt` reads the pair-swap `(a, b) ↦ (b, a)` through the **additive** fold
`a − b` as **negation**, fixing the additive unit `0` (`swap_realizes_negation`,
`zero_unique_negation_fixed`, `zero_is_diagonal_collapse`).  This section proves the
twin on this file's **multiplicative** fold `a / b`: the *same* swap is **reciprocal**,
fixing the multiplicative unit `1`.

The two foldings are one axis-generator move seen on `+` and on `·`; the
involution-fixed point is the axis unit in each case — `0` additively, `1`
multiplicatively — both materialized as the swap-fixed diagonal `{(k, k)}`.  This is
the pair-level shadow of the shared-unit identity (`theory/essays/tower_atlas.md`'s
`grand_unification`): negation and reciprocal are the one period-2 swap read by two
folds, and they fix the one unit read at `0` and at `1`. -/

/-- The pair swap `(a, b) ↦ (b, a)` — the SAME involution `NatPairToInt` reads as
    negation, here read by the multiplicative fold as reciprocal. -/
def qSwap (p : QPair) : QPair := (p.2, p.1)

/-- ★ **The swap is a period-2 involution** — `qSwap (qSwap p) = p`, the
    multiplicative-side `1/(1/x) = x`, the twin of ℤ's `−(−x) = x`. -/
theorem qSwap_involutive (p : QPair) : qSwap (qSwap p) = p := rfl

/-- Pairwise product of `QPair`s: `(a, b) · (c, d) = (a·c, b·d)` — represents
    `(a/b) · (c/d) = (a·c)/(b·d)`. -/
def qPairMul (p q : QPair) : QPair :=
  (Nat213.mul p.1 q.1, Nat213.mul p.2 q.2)

/-- ★★★ **The swap realizes reciprocal — `x · (1/x) = 1`.**  The product of a pair
    with its swap is the unit class: `(a, b) · (b, a) = (a·b, b·a) ~ qOne`, since
    `a·b = b·a`.  This is the reciprocal law `(a/b)·(b/a) = 1`, the multiplicative
    twin of ℤ's `x + (−x) = 0`.  So the swap-fold is genuinely the inverse on the `·`
    axis, exactly as it is on the `+` axis. -/
theorem qpair_mul_swap_eq_qOne (p : QPair) :
    qpairEquiv (qPairMul p (qSwap p)) qOne := by
  show Nat213.mul (Nat213.mul p.1 p.2) Nat213.one
      = Nat213.mul (Nat213.mul p.2 p.1) Nat213.one
  rw [Nat213.mul_one, Nat213.mul_one]
  exact Nat213.mul_comm p.1 p.2

/-- ★ **The unit is reciprocal-fixed** — `qSwap qOne ~ qOne`, i.e. `1/1 = 1`, the
    twin of ℤ's `−0 = 0`. -/
theorem qOne_reciprocal_fixed : qpairEquiv (qSwap qOne) qOne := rfl

/-- ★ **The diagonal collapses to the unit** — every `(k, k)` is in the unit class,
    `(k, k) ~ qOne`, since `k·1 = k·1`.  The multiplicative twin of ℤ's
    `zero_is_diagonal_collapse` (the diagonal collapses to `0`): the swap-fixed
    diagonal is the axis unit, `0` additively and `1` multiplicatively. -/
theorem qpair_diagonal_collapse (k : Nat213) : qpairEquiv (k, k) qOne := rfl

/-- ★ **The unit class is reciprocal-fixed** — if `(a, b) ~ qOne` (i.e. `a = b`) then
    `qSwap (a, b) ~ (a, b)`.  The forward inclusion of the fixed-point characterization,
    the twin of one direction of ℤ's `zero_unique_negation_fixed`.  (The converse —
    that swap-fixedness forces the unit class — is square-injectivity on `Nat213`,
    `b·b = a·a → a = b`, which the present Peano law set does not yet supply; the
    additive twin closes there by `Int` constructor analysis.) -/
theorem reciprocal_fixed_of_unit {p : QPair} (h : qpairEquiv p qOne) :
    qpairEquiv (qSwap p) p := by
  have hab : p.1 = p.2 := by
    have e : Nat213.mul p.1 Nat213.one = Nat213.mul p.2 Nat213.one := h
    rw [Nat213.mul_one, Nat213.mul_one] at e
    exact e
  show Nat213.mul p.2 p.2 = Nat213.mul p.1 p.1
  rw [hab]

/-- ★★★ **The reciprocal is the multiplicative twin of negation.**  Bundle: the pair
    swap is a period-2 involution (`1/(1/x) = x`); reading it by the multiplicative
    fold gives the reciprocal law `x · (1/x) = 1`; its fixed point is the unit `1`
    (`qOne` is reciprocal-fixed, and the unit class is fixed); and the swap-fixed
    diagonal `{(k, k)}` collapses to that unit.  Place this beside
    `NatPairToInt.swap_realizes_negation` / `zero_unique_negation_fixed` /
    `zero_is_diagonal_collapse`: one swap, two folds, two units (`0` for `+`, `1` for
    `·`) — the invert move is a single mechanism read on the two operations. -/
theorem reciprocal_is_multiplicative_twin_of_negation :
    (∀ p : QPair, qSwap (qSwap p) = p)
    ∧ (∀ p : QPair, qpairEquiv (qPairMul p (qSwap p)) qOne)
    ∧ qpairEquiv (qSwap qOne) qOne
    ∧ (∀ k : Nat213, qpairEquiv (k, k) qOne) :=
  ⟨qSwap_involutive, qpair_mul_swap_eq_qOne, qOne_reciprocal_fixed,
   qpair_diagonal_collapse⟩

end E213.Lens.Number.Nat213.Tower.NatPairToQPos
