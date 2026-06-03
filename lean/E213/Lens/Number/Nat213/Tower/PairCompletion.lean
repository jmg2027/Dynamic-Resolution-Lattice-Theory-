import E213.Lens.Number.Nat213.Peano
import E213.Lens.Number.Nat213.Tower.NatPairToQPos
import E213.Lib.Physics.Simplex.Counts

/-!
# Lens.Number.Nat213.Tower.PairCompletion — the invert move, once

`ℤ` and `ℚ_+` are founded separately — `NatPairToInt` (additive diagonal `a + d = b + c`,
swap = negation, fixing `0`) and `NatPairToQPos` (multiplicative diagonal `a · d = b · c`,
swap = reciprocal, fixing `1`).  The two constructions are visibly parallel: same
`pair + diagonal-quotient` shape, the operation the only difference.  This file makes the
parallel a *theorem* — the **invert move** as one mechanism, instantiated at `+` and `·`.

The data the move needs is a **commutative cancellative semigroup** on `Nat213`: an
associative-commutative operation with right cancellation.  **No unit is required.**
`Nat213` starts at `one` and has no additive identity, yet the additive completion (`ℤ`)
still has an identity — because the completed group's identity is not inherited from the
base, it **emerges** as the diagonal class `{(k, k)}`.  The construction is unit-free, and
the diagonal is the emergent identity in both the additive and multiplicative instances.

So the additive and multiplicative number-axes are not stacked rungs; they are one
construction (`pairEquiv` / `swap` / `combine`) read on the two operations.  The
multiplicative instance recovers `NatPairToQPos.qpairEquiv` definitionally.

All theorems ∅-axiom.
-/

namespace E213.Lens.Number.Nat213.Tower.PairCompletion

open E213.Lens.Number.Nat213.Peano (Nat213)
open E213.Lib.Physics.Simplex.Counts (NT)

/-- A **commutative cancellative semigroup** on `Nat213` — exactly the data the invert
    move consumes: associative, commutative, right-cancellative.  No unit. -/
structure CommCancelSemigroup where
  op : Nat213 → Nat213 → Nat213
  comm : ∀ a b, op a b = op b a
  assoc : ∀ a b c, op (op a b) c = op a (op b c)
  rcancel : ∀ {a b c}, op a c = op b c → a = b

/-- The completion equivalence on pairs: `(a, b) ~ (c, d) ⟺ a ∘ d = b ∘ c`.  Additive
    `op` gives `ℤ`'s diagonal `a + d = b + c`; multiplicative `op` gives `ℚ_+`'s
    `a · d = b · c` — one relation, the operation the only difference. -/
def pairEquiv (M : CommCancelSemigroup) (p q : Nat213 × Nat213) : Prop :=
  M.op p.1 q.2 = M.op p.2 q.1

/-- Reflexivity — by commutativity. -/
theorem pairEquiv_refl (M : CommCancelSemigroup) (p : Nat213 × Nat213) :
    pairEquiv M p p :=
  M.comm p.1 p.2

/-- Symmetry. -/
theorem pairEquiv_symm (M : CommCancelSemigroup) {p q : Nat213 × Nat213}
    (h : pairEquiv M p q) : pairEquiv M q p := by
  show M.op q.1 p.2 = M.op q.2 p.1
  rw [M.comm q.1 p.2, M.comm q.2 p.1]
  exact h.symm

/-- Transitivity — cross-combine the two hypotheses, reassociate, cancel the common
    factor `q.2` via `rcancel`.  The same proof shape `NatPairToQPos.qpairEquiv_trans`
    uses, now for any `CommCancelSemigroup`. -/
theorem pairEquiv_trans (M : CommCancelSemigroup) {p q r : Nat213 × Nat213}
    (h1 : pairEquiv M p q) (h2 : pairEquiv M q r) : pairEquiv M p r := by
  show M.op p.1 r.2 = M.op p.2 r.1
  apply M.rcancel (c := q.2)
  show M.op (M.op p.1 r.2) q.2 = M.op (M.op p.2 r.1) q.2
  rw [M.assoc p.1 r.2 q.2, M.comm r.2 q.2, ← M.assoc p.1 q.2 r.2]
  rw [h1]
  rw [M.assoc p.2 q.1 r.2, h2]
  rw [M.comm q.2 r.1, ← M.assoc p.2 r.1 q.2]

/-- The pair swap `(a, b) ↦ (b, a)` — the inverse-realising involution (negation for
    `+`, reciprocal for `·`). -/
def swap (p : Nat213 × Nat213) : Nat213 × Nat213 := (p.2, p.1)

/-- The swap is a period-2 involution. -/
theorem swap_involutive (p : Nat213 × Nat213) : swap (swap p) = p := rfl

/-- Component-wise combination: `(a, b) ∘ (c, d) = (a ∘ c, b ∘ d)` — the completed
    group's operation. -/
def combine (M : CommCancelSemigroup) (p q : Nat213 × Nat213) : Nat213 × Nat213 :=
  (M.op p.1 q.1, M.op p.2 q.2)

/-- ★ **The diagonal is a single class** — `(a, a) ~ (b, b)` for all `a, b`, with no
    unit assumed.  The diagonal is the emergent identity of the completed group. -/
theorem diagonal_single_class (M : CommCancelSemigroup) (a b : Nat213) :
    pairEquiv M (a, a) (b, b) := rfl

/-- ★★★ **The swap is the inverse — `x ∘ inv(x)` lands in the identity class.**  For any
    pair `p`, `combine p (swap p) ~ (k, k)`: its two components `p.1 ∘ p.2` and
    `p.2 ∘ p.1` are equal by commutativity, so the product of an element with its swap is
    on the diagonal — the emergent group identity.  Unit-free: this holds with no
    identity element in the base semigroup.  This is `x + (−x) = 0` for the additive
    instance and `x · (1/x) = 1` for the multiplicative one, in one theorem. -/
theorem combine_swap_equiv_diagonal (M : CommCancelSemigroup) (p : Nat213 × Nat213)
    (k : Nat213) : pairEquiv M (combine M p (swap p)) (k, k) := by
  show M.op (M.op p.1 p.2) k = M.op (M.op p.2 p.1) k
  rw [M.comm p.1 p.2]

/-- The **additive** instance `(Nat213, +)` — its pair-completion is the `ℤ` model
    (`a + d = b + c`, swap = negation). -/
def addCCS : CommCancelSemigroup where
  op := Nat213.add
  comm := Nat213.add_comm
  assoc := Nat213.add_assoc
  rcancel := Nat213.add_right_cancel

/-- The **multiplicative** instance `(Nat213, ·)` — its pair-completion is the `ℚ_+`
    model (`a · d = b · c`, swap = reciprocal). -/
def mulCCS : CommCancelSemigroup where
  op := Nat213.mul
  comm := Nat213.mul_comm
  assoc := Nat213.mul_assoc
  rcancel := Nat213.mul_right_cancel

/-- ★ The multiplicative instance's completion **is** `NatPairToQPos.qpairEquiv` — the
    generic invert move at `op = ·` recovers the concrete `ℚ_+` relation definitionally. -/
theorem mulCCS_recovers_qpairEquiv (p q : Nat213 × Nat213) :
    pairEquiv mulCCS p q ↔ NatPairToQPos.qpairEquiv p q := Iff.rfl

/-- ★★★ **The invert move is one mechanism, instantiated at `+` and at `·`.**  Bundle:
    the pair-completion `pairEquiv M` is an equivalence relation for *every*
    `CommCancelSemigroup M` (reflexive here; `pairEquiv_symm` / `pairEquiv_trans` above);
    the swap `(a, b) ↦ (b, a)` is the inverse, with `combine p (swap p)` landing in the
    emergent identity (diagonal) class — `unit-free`; and the multiplicative instance
    recovers the concrete `ℚ_+` relation `NatPairToQPos.qpairEquiv`.  The additive
    instance `addCCS` is the same construction at `op = +` (the `ℤ` model).

    So `ℤ` and `ℚ_+` are not stacked rungs of a linear tower — they are one closure move
    (`pairEquiv` / `swap` / `combine`) read on the two operations `+` and `·`, the
    operation the only difference, the group identity emerging as the diagonal in both. -/
theorem invert_is_one_move :
    (∀ (M : CommCancelSemigroup) (p : Nat213 × Nat213), pairEquiv M p p)
    ∧ (∀ (M : CommCancelSemigroup) (p : Nat213 × Nat213) (k : Nat213),
        pairEquiv M (combine M p (swap p)) (k, k))
    ∧ (∀ p q : Nat213 × Nat213, pairEquiv mulCCS p q ↔ NatPairToQPos.qpairEquiv p q) :=
  ⟨pairEquiv_refl, combine_swap_equiv_diagonal, mulCCS_recovers_qpairEquiv⟩

/-! ### The period is `NT`: why the involution is order 2 and not order `k`

The invert move's inverse is the *swap* of a **pair** — an ordered tuple with exactly
`NT = 2` positions.  The swap permutes those positions, so it generates the symmetric
group on `NT = 2` letters, which has order `NT = 2`: the swap is an involution
(`swap_involutive`, order divides 2) and it is not the identity (`swap_ne_id`, order ≠ 1),
hence its order is *exactly* `NT`.  There is no order-3 (or order-`k`, `k ≠ 2`) sign
structure here because there are only `NT` positions to permute — period-2 is forced by
`NT = 2`, not chosen. -/

/-- The swap genuinely moves an off-diagonal pair — so its order is not 1. -/
theorem swap_ne_id : swap (Nat213.one, Nat213.two) ≠ (Nat213.one, Nat213.two) := by
  decide

/-- ★★★ **The swap has order exactly `NT = 2`.**  Involution (`swap_involutive`, order
    divides `NT`) and non-identity (`swap_ne_id`, order ≠ 1), with `NT = 2`.  A pair has
    `NT` positions; the inverse-realising swap permutes them; its order is exactly `NT`.
    So the period-2 sign of `ℤ` (and the period-2 reciprocal of `ℚ_+`) is *forced* by the
    count `NT = 2` — there is no room for a period-`k`, `k ≠ 2`, involution on a pair. -/
theorem swap_order_eq_NT :
    (∀ p : Nat213 × Nat213, swap (swap p) = p)
    ∧ (∃ p : Nat213 × Nat213, swap p ≠ p)
    ∧ NT = 2 :=
  ⟨swap_involutive, ⟨(Nat213.one, Nat213.two), swap_ne_id⟩, rfl⟩

end E213.Lens.Number.Nat213.Tower.PairCompletion
