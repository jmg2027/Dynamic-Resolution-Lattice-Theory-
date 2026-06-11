import E213.Meta.Int213.Core
import E213.Meta.Nat.AddMod213

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

/-! ## §2 — everything forgotten: the witness layer

Dropping *all* properties (commutativity, associativity,
cancellation, exchange) and re-deriving exposes the true jobs:

1. The question splits: `f a x = b` and `f x a = b` are different
   questions — **commutativity's first job is fusing the two pair
   kinds** (`question_fuse`); the `^` root/log split originates here,
   at step zero.
2. The cross-equation is not primitive: the **witness relation**
   (`sameWitness` — the two questions share a solving `x`) is the
   original, free to state and symmetric for any `f`; the
   cross-equation is its shadow, faithful under **action-commutation**
   (`f a (f c x) = f c (f a x)`, strictly weaker than comm+assoc —
   `action_comm_of_comm_assoc` shows those merely supply it) plus
   cancellation for the converse.
3. **Cancellation's true job is witness uniqueness** — transitivity of
   the witness relation *is* uniqueness of the middle witness
   (`sameWitness_trans`).
4. **The lift's true actor is the medial law alone**: "the witness of
   the product is the product of the witnesses" (`pairLift_witness`)
   needs neither commutativity nor associativity directly. -/

/-- Without commutativity the question bifurcates; with it the two
    pair kinds fuse. -/
theorem question_fuse (f : Nat → Nat → Nat)
    (hcomm : ∀ x y, f x y = f y x) (a x b : Nat) :
    f a x = b ↔ f x a = b := by rw [hcomm]

/-- The primary relation, property-free: the two questions share a
    solving witness. -/
def sameWitness (f : Nat → Nat → Nat) (p q : Nat × Nat) : Prop :=
  ∃ x, f p.1 x = p.2 ∧ f q.1 x = q.2

/-- Symmetry of the witness relation is free, for any `f`. -/
theorem sameWitness_symm (f : Nat → Nat → Nat) {p q : Nat × Nat}
    (h : sameWitness f p q) : sameWitness f q p := by
  obtain ⟨x, h1, h2⟩ := h
  exact ⟨x, h2, h1⟩

/-- Reflexivity holds exactly where a witness exists — already
    informative: the witnessed pairs are the old layer. -/
theorem sameWitness_refl (f : Nat → Nat → Nat) {p : Nat × Nat}
    (h : ∃ x, f p.1 x = p.2) : sameWitness f p p := by
  obtain ⟨x, hx⟩ := h
  exact ⟨x, hx, hx⟩

/-- ★★★★ **Cancellation's true job: witness uniqueness.**
    Transitivity of the witness relation is exactly uniqueness of the
    middle pair's witness — no commutativity, no associativity. -/
theorem sameWitness_trans (f : Nat → Nat → Nat) {p q r : Nat × Nat}
    (hcancel : ∀ x y, f q.1 x = f q.1 y → x = y)
    (h1 : sameWitness f p q) (h2 : sameWitness f q r) :
    sameWitness f p r := by
  obtain ⟨x, hx1, hx2⟩ := h1
  obtain ⟨y, hy1, hy2⟩ := h2
  have hxy : x = y := hcancel x y (hx2.trans hy1.symm)
  exact ⟨x, hx1, hxy ▸ hy2⟩

/-- ★★★★ **The cross-equation is the witness relation's shadow**,
    cast by action-commutation alone (`f a (f c x) = f c (f a x)`) —
    strictly weaker than commutativity + associativity. -/
theorem crossEq_of_sameWitness (f : Nat → Nat → Nat)
    (hact : ∀ a c x, f a (f c x) = f c (f a x))
    {p q : Nat × Nat} (h : sameWitness f p q) : pairEq f p q := by
  obtain ⟨x, h1, h2⟩ := h
  show f p.1 q.2 = f q.1 p.2
  rw [← h2, ← h1]
  exact hact p.1 q.1 x

/-- The shadow is faithful: with action-commutation and cancellation
    at the witnessed slot, the cross-equation detects the shared
    witness wherever one exists. -/
theorem sameWitness_of_crossEq (f : Nat → Nat → Nat)
    (hact : ∀ a c x, f a (f c x) = f c (f a x))
    {p q : Nat × Nat}
    (hcancel : ∀ x y, f p.1 x = f p.1 y → x = y)
    (hw : ∃ x, f p.1 x = p.2)
    (h : pairEq f p q) : sameWitness f p q := by
  obtain ⟨x, hx⟩ := hw
  refine ⟨x, hx, ?_⟩
  have h1 : f p.1 q.2 = f q.1 p.2 := h
  rw [← hx] at h1
  have h2 : f p.1 q.2 = f p.1 (f q.1 x) :=
    h1.trans (hact q.1 p.1 x)
  exact (hcancel _ _ h2).symm

/-- Commutativity + associativity merely *supply* action-commutation. -/
theorem action_comm_of_comm_assoc (f : Nat → Nat → Nat)
    (hcomm : ∀ x y, f x y = f y x)
    (hassoc : ∀ x y z, f (f x y) z = f x (f y z)) :
    ∀ a c x, f a (f c x) = f c (f a x) := by
  intro a c x
  calc f a (f c x)
      = f (f a c) x := (hassoc _ _ _).symm
    _ = f (f c a) x := by rw [hcomm a c]
    _ = f c (f a x) := hassoc _ _ _

/-- ★★★★ **The lift's true actor is the medial law alone**: the
    witness of the lifted pair is the lift of the witnesses —
    `f (f a c) (f x y) = f (f a x) (f c y)` is all it takes, with
    neither commutativity nor associativity assumed directly. -/
theorem pairLift_witness (f : Nat → Nat → Nat)
    (hmedial : ∀ a b c d, f (f a b) (f c d) = f (f a c) (f b d))
    {p q : Nat × Nat} {x y : Nat}
    (hx : f p.1 x = p.2) (hy : f q.1 y = q.2) :
    f (pairLift f p q).1 (f x y) = (pairLift f p q).2 := by
  show f (f p.1 q.1) (f x y) = f p.2 q.2
  rw [hmedial p.1 q.1 x y, hx, hy]

/-! ## §3 — the list picture: progressive vs wrapping operations

ℕ as the unit-started, unit-spaced ordered list; the order itself is
the +-witness question (`a ≤ b ↔ ∃x, a+x=b`), so everything below is
an ℕ-internal statement about `f`.  An operation that "only moves
backward along the list, without merging" — strictly monotone in the
unknown slot — gets §2's cancellation **for free from the list
structure** (`cancel_of_strictMono`): the list pays the price.  A
*wrapping* operation (mod) keeps every free step of §2 and the medial
lift (`modAdd_medial`), but loses pointwise cancellation
(`modAdd_cancel_fails`): its witness sets are arithmetic
progressions, so its pairs mint **periodic classes** (the ℤ/n world)
rather than points — and the wrap itself is not a new primitive: it
is the fiber-position readout of a progressive question
(`NatDiv213.div_sandwich`'s remainder). -/

/-- "Backward only, no merging" (strict monotonicity in the unknown
    slot) yields cancellation — the §2 price, paid by the list. -/
theorem cancel_of_strictMono (f : Nat → Nat → Nat) (a : Nat)
    (hmono : ∀ x y, x < y → f a x < f a y) :
    ∀ x y, f a x = f a y → x = y := by
  intro x y h
  rcases Nat.lt_or_ge x y with hlt | hge
  · exact absurd (h ▸ hmono x y hlt) (Nat.lt_irrefl _)
  · rcases Nat.lt_or_ge y x with hlt' | hge'
    · exact absurd (h ▸ hmono y x hlt') (Nat.lt_irrefl _)
    · exact Nat.le_antisymm hge' hge

/-- Wrapping loses pointwise cancellation: mod-2 addition merges the
    witnesses 0 and 2.  Its witness sets are arithmetic progressions —
    the pair of a wrapping question is a periodic class, not a point. -/
theorem modAdd_cancel_fails :
    (0 + 0) % 2 = (0 + 2) % 2 ∧ (0 : Nat) ≠ 2 :=
  ⟨rfl, fun h => Nat.noConfusion h⟩

/-- The wrap keeps the lift: mod-addition satisfies the medial law,
    so `pairLift_witness` applies unchanged.  Only pointwise witness
    uniqueness is lost (it survives class-wise — the ℤ/n world). -/
theorem modAdd_medial (n : Nat) (a b c d : Nat) :
    ((a + b) % n + (c + d) % n) % n
    = ((a + c) % n + (b + d) % n) % n := by
  rw [← E213.Meta.Nat.AddMod213.add_mod_gen (a + b) (c + d) n,
      ← E213.Meta.Nat.AddMod213.add_mod_gen (a + c) (b + d) n,
      Nat.add_assoc a b (c + d), ← Nat.add_assoc b c d,
      Nat.add_comm b c, Nat.add_assoc c b d,
      ← Nat.add_assoc a c (b + d)]

end E213.Meta.Nat.PairOp
