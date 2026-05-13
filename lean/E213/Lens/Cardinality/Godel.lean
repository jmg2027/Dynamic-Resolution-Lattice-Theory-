import E213.Theory.Raw
import E213.Lens.Cardinality.Pair
import E213.Lens.Cardinality.Countable
import E213.Prelude

/-!
# Infinity.Godel: Σ2 — Raw → ℕ injective encoding

Explicit Gödel numbering of `Tree` (the raw inductive type
underlying `Raw`) by

  a     → 0
  b     → 1
  slash x y → 2 + 2 · pair(toNat x, toNat y)

where `pair` is the injective pairing from `Infinity.Pair`.

Parity + range separate the three constructors:
- `a.toNat = 0`, `b.toNat = 1`,
- `slash.toNat ≥ 2` and always even.

Injectivity is structural induction on `Tree`, using
`pair_injective_4` to split the slash branch into
coordinate-wise subgoals for the IH.

`Raw.toNat` is the Gödel number of the underlying canonical
`Tree`.  Injectivity lifts immediately via `Subtype.val`.
Combined with `Σ3` (`rawTower_injective`) this establishes
`|Raw| = |ℕ|` — Raw is countable.
-/

namespace E213.Theory.Internal

open E213.Lens.Cardinality (pair pair_injective_4)

/-- Gödel numbering of `Tree`. -/
def Tree.toNat : Tree → Nat
  | .a         => 0
  | .b         => 1
  | .slash x y => 2 + 2 * pair (Tree.toNat x) (Tree.toNat y)

theorem Tree.toNat_a : Tree.a.toNat = 0 := rfl
theorem Tree.toNat_b : Tree.b.toNat = 1 := rfl
theorem Tree.toNat_slash (x y : Tree) :
    (Tree.slash x y).toNat
      = 2 + 2 * pair x.toNat y.toNat := rfl

end E213.Theory.Internal

namespace E213.Theory.Internal

open E213.Lens.Cardinality (pair pair_injective_4)

/-- **Σ2 (Tree level).**  Gödel numbering is injective on
    Tree. -/
theorem Tree.toNat_injective :
    ∀ t1 t2 : Tree, t1.toNat = t2.toNat → t1 = t2 := by
  intro t1
  induction t1 with
  | a =>
      intro t2 heq
      cases t2 with
      | a => rfl
      | b =>
          have h : (0 : Nat) = 1 := heq
          exact Nat.noConfusion h
      | slash x y =>
          have h0 : (0 : Nat) = 2 + 2 * pair x.toNat y.toNat := heq
          have h1 : (0 : Nat) = 2 * pair x.toNat y.toNat + 2 :=
            h0.trans (Nat.add_comm 2 (2 * pair x.toNat y.toNat))
          exact Nat.noConfusion h1
  | b =>
      intro t2 heq
      cases t2 with
      | a =>
          have h : (1 : Nat) = 0 := heq
          exact Nat.noConfusion h
      | b => rfl
      | slash x y =>
          have h0 : (1 : Nat) = 2 + 2 * pair x.toNat y.toNat := heq
          have h1 : (1 : Nat) = 2 * pair x.toNat y.toNat + 2 :=
            h0.trans (Nat.add_comm 2 (2 * pair x.toNat y.toNat))
          exact Nat.noConfusion (Nat.succ.inj h1)
  | slash x1 y1 ihx ihy =>
      intro t2 heq
      cases t2 with
      | a =>
          have h0 : 2 + 2 * pair x1.toNat y1.toNat = (0 : Nat) := heq
          have h1 : 2 * pair x1.toNat y1.toNat + 2 = (0 : Nat) :=
            (Nat.add_comm 2 (2 * pair x1.toNat y1.toNat)).symm.trans h0
          exact Nat.noConfusion h1
      | b =>
          have h0 : 2 + 2 * pair x1.toNat y1.toNat = (1 : Nat) := heq
          have h1 : 2 * pair x1.toNat y1.toNat + 2 = (1 : Nat) :=
            (Nat.add_comm 2 (2 * pair x1.toNat y1.toNat)).symm.trans h0
          exact Nat.noConfusion (Nat.succ.inj h1)
      | slash x2 y2 =>
          have h0 : 2 + 2 * pair x1.toNat y1.toNat
                  = 2 + 2 * pair x2.toNat y2.toNat := heq
          have h1 : 2 * pair x1.toNat y1.toNat + 2
                  = 2 * pair x2.toNat y2.toNat + 2 :=
            ((Nat.add_comm 2 (2 * pair x1.toNat y1.toNat)).symm.trans h0).trans
              (Nat.add_comm 2 (2 * pair x2.toNat y2.toNat))
          have h2 : 2 * pair x1.toNat y1.toNat = 2 * pair x2.toNat y2.toNat :=
            Nat.succ.inj (Nat.succ.inj h1)
          have hp : pair x1.toNat y1.toNat = pair x2.toNat y2.toNat :=
            Nat.eq_of_mul_eq_mul_left (by decide) h2
          obtain ⟨hxn, hyn⟩ := pair_injective_4 _ _ _ _ hp
          rw [ihx x2 hxn, ihy y2 hyn]

end E213.Theory.Internal

namespace E213.Theory

open E213.Theory.Internal

/-- **Σ2 (Raw level).**  Raw's Gödel number = underlying
    Tree's Gödel number. -/
def Raw.toNat (r : Raw) : Nat := r.val.toNat

/-- Injectivity lifts from `Tree.toNat_injective` via the
    subtype projection. -/
theorem Raw.toNat_injective : Function.Injective Raw.toNat := by
  intro r1 r2 heq
  have hval : r1.val = r2.val :=
    Tree.toNat_injective r1.val r2.val heq
  exact Subtype.ext hval

end E213.Theory

namespace E213.Lens.Cardinality

open E213.Theory

/-- **Σ2 packaged.**  Raw injects into ℕ. -/
theorem raw_at_most_countable :
    ∃ f : Raw → Nat, Function.Injective f :=
  ⟨Raw.toNat, Raw.toNat_injective⟩

/-- **Σ2 ∧ Σ3: Raw is equipotent to ℕ.**  Concrete witnesses
    in both directions — Gödel numbering (`Raw.toNat`) and
    right-leaning tower (`rawTower`) — establish mutual
    injectivity.  Raw is therefore countable at the
    Lean-4-core level, using no cardinality/choice axiom. -/
theorem raw_equipotent_nat :
    (∃ f : Nat → Raw, Function.Injective f)
      ∧ (∃ g : Raw → Nat, Function.Injective g) :=
  ⟨raw_at_least_countable, raw_at_most_countable⟩

end E213.Lens.Cardinality
