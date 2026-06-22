import E213.Theory.Raw.API

/-!
# UniversalDistinguishing — the distinguishing schema `DStr` (∅-axiom)

The structured-rival exclusion (`research-notes/frontiers/the_distinguishing_schema.md`) reframed:
instead of excluding rival primitives one class at a time (an open `∀ rival`), characterize the
distinguishing by a **schema** `DStr` and a universal property, so that exhaustiveness becomes a
*dichotomy* (satisfy the schema ⟹ canonically `Raw`; else fail a *named* clause), not an enumeration.

`DStr` is deliberately **weaker** than `Lens` / `HasDistinguishing`: it does **not** name
binarity-as-a-total-op, commutativity, or super-linear growth.  Its pairing `op` is **partial**
(defined exactly on distinct pairs — distinctness in the *type*), faithful only **up to swap**.  Yet
`Raw` satisfies it (`rawDStr`), and binary / commutative (`Raw.slash_comm`) / super-linear growth are
then *derived*, not assumed — the advance over `Lens.view_unique` (whose category presupposes the
binary commutative `combine`, the skeptic's circularity charge).

  - **D1** `e_ne` — the carrier distinguishes (≥ 2 elements).
  - **D2** `op : (x y) → x ≠ y → α` — a *partial* pairing (a unary or a total `op x x` rival is not
    even a `DStr`, by signature — this is how `RivalArity`'s corners become signature failures).
  - **D3** `op_faithful` — faithful up to swap (⟹ commutativity of the free object is a theorem).
  - **D4** `op_ne_operand` — a pairing is never its own operand (freeness / no collapse).
  - **D5** `rank_op` — `op` strictly increases a ℕ-rank (well-founded generation).

`rawDStr` fills every field from existing PURE theorems; the keystone D3 is `Raw.slash_inj`.  ∅-axiom.
-/

namespace E213.Lens.UniversalDistinguishing

open E213.Theory (Raw)

/-- **The distinguishing schema.**  A carrier that distinguishes, with a *partial* faithful
    well-founded pairing.  Deliberately weaker than `Lens`/`HasDistinguishing`: binarity-as-a-total-op,
    commutativity, and super-linear growth are *not* fields — they are consequences for the free
    object. -/
structure DStr (α : Type) where
  e₁ : α
  e₂ : α
  e_ne : e₁ ≠ e₂
  op : (x y : α) → x ≠ y → α
  op_ne_operand : ∀ (x y : α) (h : x ≠ y), op x y h ≠ x ∧ op x y h ≠ y
  op_faithful : ∀ (x y : α) (hxy : x ≠ y) (u v : α) (huv : u ≠ v),
      op x y hxy = op u v huv → (x = u ∧ y = v) ∨ (x = v ∧ y = u)
  rank : α → Nat
  rank_op : ∀ (x y : α) (h : x ≠ y),
      rank x < rank (op x y h) ∧ rank y < rank (op x y h)

/-- ★★★ **`Raw` is a `DistinguishingStructure`** — under the *weaker* axioms (no binarity-as-total-op,
    no commutativity, no growth field assumed).  Every field is an existing PURE theorem:
    D1 = `PrimitiveTower.a_ne_b`, D2 = `Raw.slash`, D3 = `Raw.slash_inj` (the keystone, faithful up to
    swap), D4 = `Raw.slash_ne_left/right`, D5 = `Lambek.depth_drops`.  That commutativity is *not* a
    field yet `Raw.slash_comm` holds is the point: it is *derived*, not assumed. -/
def rawDStr : DStr Raw where
  e₁ := Raw.a
  e₂ := Raw.b
  e_ne := E213.Theory.Raw.PrimitiveTower.a_ne_b
  op := Raw.slash
  op_ne_operand := fun x y h => ⟨Raw.slash_ne_left x y h, Raw.slash_ne_right x y h⟩
  op_faithful := fun _ _ _ _ _ _ he => Raw.slash_inj he
  rank := Raw.depth
  rank_op := fun x y h => E213.Theory.Raw.Lambek.depth_drops x y h

/-- A `DStr` carrier is **generated** when every element is a base point or a pairing — the part of a
    structure the distinguishing actually produces (the universal property's domain of iso). -/
def Generated {α : Type} (N : DStr α) : Prop :=
  ∀ z : α, z = N.e₁ ∨ z = N.e₂ ∨ ∃ (x y : α) (h : x ≠ y), z = N.op x y h

/-- ★ **`Raw` is generated** — every `Raw` is an atom or a slash, so `Raw` is the *free* `DStr` (the
    candidate initial object of the schema). -/
theorem rawDStr_generated : Generated rawDStr := by
  intro z
  induction z using Raw.rec with
  | a => exact Or.inl rfl
  | b => exact Or.inr (Or.inl rfl)
  | slash x y h _ _ => exact Or.inr (Or.inr ⟨x, y, h, rfl⟩)

end E213.Lens.UniversalDistinguishing
