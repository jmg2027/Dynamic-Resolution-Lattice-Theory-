import E213.Meta.Int213.Core

/-!
# PairOp — the pair layer of an arbitrary (ℕ,ℕ)→ℕ operation

The generic step-ladder
(`research-notes/frontiers/numbersystem_square.md` "Ontology"): for
**any** binary operation `f : ℕ → ℕ → ℕ` (+, ×, ^, tetration, …), the
question `f a x = b` mints pairs, and the pair layer is built one
step at a time, each step paying a stated price in properties of `f`:

| step | price |
|---|---|
| the pair `(a,b)` | free (any `f`) |
| the pair relation `pairEq` | free to state |
| `pairEq` reflexive, symmetric | free (any `f`) |
| `pairEq` transitive | commutativity + associativity + cancellation at the middle slot (`pairEq_trans`) |
| the slotwise lift of `f` to pairs | free to define (`pairLift`) |
| the lift respects the relation | commutativity + associativity (`exchange` → `pairLift_congr`) |
| lifting a *different* operation | the interaction law between the two (distribution) — next rung, open |

Instantiations: `f = +` gives the difference-pair relation
(`pairEq_add_iff`, = `subNatNat_eq_iff`); `f = ×` gives the
ratio-pair cross-equation definitionally (`pairEq_mul_iff`).  For
`f = ^` the free steps still stand and the priced steps lose their
generic proofs (no commutativity) — whether `pairEq ^` is
nevertheless transitive over ℕ for a *different* reason (unique
factorization) is an open brick: the first place where "holds" and
"holds for the generic reason" may split.

All ∅-axiom.
-/

namespace E213.Meta.Nat.PairOp

/-- The pair relation of a binary operation:
    `(a,b) ≈f (c,d) := f a d = f c b` — the cross-equation, uniform
    in `f` (`+` cross-sum, `×` cross-product, …). -/
def pairEq (f : Nat → Nat → Nat) (p q : Nat × Nat) : Prop :=
  f p.1 q.2 = f q.1 p.2

/-- Reflexivity is free, for any operation. -/
theorem pairEq_refl (f : Nat → Nat → Nat) (p : Nat × Nat) :
    pairEq f p p := rfl

/-- Symmetry is free, for any operation. -/
theorem pairEq_symm (f : Nat → Nat → Nat) {p q : Nat × Nat}
    (h : pairEq f p q) : pairEq f q p := h.symm

/-- The exchange (medial) law `f (f a b) (f c d) = f (f a c) (f b d)`,
    bought with commutativity + associativity. -/
theorem exchange (f : Nat → Nat → Nat)
    (hcomm : ∀ x y, f x y = f y x)
    (hassoc : ∀ x y z, f (f x y) z = f x (f y z))
    (a b c d : Nat) :
    f (f a b) (f c d) = f (f a c) (f b d) := by
  calc f (f a b) (f c d)
      = f a (f b (f c d)) := hassoc _ _ _
    _ = f a (f (f b c) d) := by rw [← hassoc b c d]
    _ = f a (f (f c b) d) := by rw [hcomm b c]
    _ = f a (f c (f b d)) := by rw [hassoc c b d]
    _ = f (f a c) (f b d) := (hassoc _ _ _).symm

/-- ★★★★ **Transitivity is bought, not free**: commutativity,
    associativity, and cancellation *at the middle pair's second
    slot* (`q.2`) — for `×` that cancellation needs `0 < q.2`, which
    is why ratio transitivity required positive resolution. -/
theorem pairEq_trans (f : Nat → Nat → Nat)
    (hcomm : ∀ x y, f x y = f y x)
    (hassoc : ∀ x y z, f (f x y) z = f x (f y z))
    {p q r : Nat × Nat}
    (hcancel : ∀ x y, f q.2 x = f q.2 y → x = y)
    (h1 : pairEq f p q) (h2 : pairEq f q r) : pairEq f p r := by
  apply hcancel
  have hc1 : f p.1 q.2 = f q.1 p.2 := h1
  have hc2 : f q.1 r.2 = f r.1 q.2 := h2
  calc f q.2 (f p.1 r.2)
      = f (f q.2 p.1) r.2 := (hassoc _ _ _).symm
    _ = f (f p.1 q.2) r.2 := by rw [hcomm q.2 p.1]
    _ = f (f q.1 p.2) r.2 := by rw [hc1]
    _ = f q.1 (f p.2 r.2) := hassoc _ _ _
    _ = f q.1 (f r.2 p.2) := by rw [hcomm p.2 r.2]
    _ = f (f q.1 r.2) p.2 := (hassoc _ _ _).symm
    _ = f (f r.1 q.2) p.2 := by rw [hc2]
    _ = f r.1 (f q.2 p.2) := hassoc _ _ _
    _ = f r.1 (f p.2 q.2) := by rw [hcomm q.2 p.2]
    _ = f (f r.1 p.2) q.2 := (hassoc _ _ _).symm
    _ = f q.2 (f r.1 p.2) := hcomm _ _

/-- The operation lifts to its own pairs **slotwise** — free to
    define, for any operation. -/
def pairLift (f : Nat → Nat → Nat) (p q : Nat × Nat) : Nat × Nat :=
  (f p.1 q.1, f p.2 q.2)

/-- ★★★★ The slotwise lift respects the pair relation in the left
    argument — bought with commutativity + associativity (the
    exchange law); no cancellation needed. -/
theorem pairLift_congr_left (f : Nat → Nat → Nat)
    (hcomm : ∀ x y, f x y = f y x)
    (hassoc : ∀ x y z, f (f x y) z = f x (f y z))
    {p p' : Nat × Nat} (q : Nat × Nat) (h : pairEq f p p') :
    pairEq f (pairLift f p q) (pairLift f p' q) := by
  show f (f p.1 q.1) (f p'.2 q.2) = f (f p'.1 q.1) (f p.2 q.2)
  calc f (f p.1 q.1) (f p'.2 q.2)
      = f (f p.1 p'.2) (f q.1 q.2) := exchange f hcomm hassoc _ _ _ _
    _ = f (f p'.1 p.2) (f q.1 q.2) := by rw [show f p.1 p'.2 = f p'.1 p.2 from h]
    _ = f (f p'.1 q.1) (f p.2 q.2) := exchange f hcomm hassoc _ _ _ _

/-- Right-argument congruence, from the left one via commutativity of
    the lift's slots. -/
theorem pairLift_congr_right (f : Nat → Nat → Nat)
    (hcomm : ∀ x y, f x y = f y x)
    (hassoc : ∀ x y z, f (f x y) z = f x (f y z))
    (p : Nat × Nat) {q q' : Nat × Nat} (h : pairEq f q q') :
    pairEq f (pairLift f p q) (pairLift f p q') := by
  show f (f p.1 q.1) (f p.2 q'.2) = f (f p.1 q'.1) (f p.2 q.2)
  calc f (f p.1 q.1) (f p.2 q'.2)
      = f (f p.1 p.2) (f q.1 q'.2) := exchange f hcomm hassoc _ _ _ _
    _ = f (f p.1 p.2) (f q'.1 q.2) := by rw [show f q.1 q'.2 = f q'.1 q.2 from h]
    _ = f (f p.1 q'.1) (f p.2 q.2) := exchange f hcomm hassoc _ _ _ _

/-- Instantiation at `+`: the pair relation **is** the difference-pair
    cross-equation, i.e. equality of the `subNatNat` readouts. -/
theorem pairEq_add_iff (A B C D : Nat) :
    pairEq Nat.add (A, B) (C, D)
    ↔ Int.subNatNat A B = Int.subNatNat C D :=
  (E213.Meta.Int213.subNatNat_eq_iff A B C D).symm

/-- Instantiation at `×`: the pair relation is the ratio cross-product
    equation, definitionally. -/
theorem pairEq_mul_iff (A B C D : Nat) :
    pairEq Nat.mul (A, B) (C, D) ↔ A * D = C * B :=
  Iff.rfl

end E213.Meta.Nat.PairOp
