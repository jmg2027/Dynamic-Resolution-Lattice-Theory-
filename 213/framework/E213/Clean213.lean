/-!
# 213: Formal Foundation

## Axiom (single primitive)

Given two objects, there exists a relation object between them.

## Formal statement

`Raw` is an inductive type with two constructors:
- `object : Fin 2 → Raw`: base objects (two of them, from the axiom's "two").
- `relation : Raw → Raw → Raw`: binary relation object between two Raw.

The axiom's "two" is captured by `Reachable` derivation:
a relation object is Reachable only from two distinct Reachable objects.

The third entity (a relation object) is not postulated — it is produced
by applying `relation` to the two base objects. See `third_object_exists`.

## Consequences

- Identity (=) is not a primitive.
- Apartness (≠) is used only as Lean's technical encoding of "two".
- `relation x x` (same-input case) is not Reachable (axiom scope).
-/

-- ═══ Section 1: Primitive Type ═══

inductive Raw where
  | object   : Fin 2 → Raw
  | relation : Raw → Raw → Raw
  deriving DecidableEq, Repr

-- ═══ Section 2: Reachable (axiom derivation) ═══

inductive Reachable : Raw → Prop where
  | base : (i : Fin 2) → Reachable (.object i)
  | step : Reachable x → Reachable y → x ≠ y →
           Reachable (.relation x y)

-- ═══ Section 3: Well-formedness ═══

def Raw.wellFormed : Raw → Prop
  | .object _     => True
  | .relation x y => x ≠ y ∧ x.wellFormed ∧ y.wellFormed

/-- Structural-recursive decidability (avoids `Raw.rec` in code gen). -/
def Raw.decWF : (x : Raw) → Decidable x.wellFormed
  | .object _     => .isTrue trivial
  | .relation a b =>
      have _ha := Raw.decWF a
      have _hb := Raw.decWF b
      show Decidable (a ≠ b ∧ a.wellFormed ∧ b.wellFormed) from inferInstance

instance : DecidablePred Raw.wellFormed := Raw.decWF

-- ═══ Section 4: Characterization ═══

theorem reachable_of_wellFormed :
    ∀ x : Raw, x.wellFormed → Reachable x
  | .object i,   _ => .base i
  | .relation a b, h =>
      let ⟨hne, ha, hb⟩ := h
      .step (reachable_of_wellFormed a ha)
            (reachable_of_wellFormed b hb)
            hne

theorem wellFormed_of_reachable {x : Raw} :
    Reachable x → x.wellFormed := by
  intro h
  induction h with
  | base _ => exact trivial
  | step _ _ hne ihx ihy => exact ⟨hne, ihx, ihy⟩

theorem reachable_iff_wellFormed (x : Raw) :
    Reachable x ↔ x.wellFormed :=
  ⟨wellFormed_of_reachable, reachable_of_wellFormed x⟩

instance : DecidablePred Reachable := fun x =>
  decidable_of_iff x.wellFormed (reachable_iff_wellFormed x).symm

-- ═══ Section 5: Core Theorems ═══

theorem relation_injective {a b c d : Raw} :
    Raw.relation a b = Raw.relation c d → a = c ∧ b = d := by
  intro h; injection h with h1 h2; exact ⟨h1, h2⟩

theorem no_self_relation_reachable (x : Raw) :
    ¬ Reachable (.relation x x) := by
  rw [reachable_iff_wellFormed]
  simp [Raw.wellFormed]

theorem reachable_relation_inv {x y : Raw} :
    Reachable (.relation x y) → Reachable x ∧ Reachable y ∧ x ≠ y := by
  intro h
  rw [reachable_iff_wellFormed] at h
  obtain ⟨hne, hx, hy⟩ := h
  refine ⟨?_, ?_, hne⟩
  all_goals rw [reachable_iff_wellFormed]; assumption

-- ═══ Section 6: Depth ═══

def Raw.depth : Raw → Nat
  | .object _     => 0
  | .relation x y => 1 + max x.depth y.depth

theorem relation_depth_gt {x y : Raw} (_ : x ≠ y) :
    (Raw.relation x y).depth > x.depth := by
  simp [Raw.depth]; omega

-- ═══ Section 7: Lens ═══

structure Lens (α : Type) where
  objValue : Fin 2 → α
  combine  : α → α → α

def Lens.view {α : Type} (L : Lens α) : Raw → α
  | .object i     => L.objValue i
  | .relation x y => L.combine (L.view x) (L.view y)

-- ═══ Section 8: Canonical Lenses ═══

def Lens.depth : Lens Nat :=
  ⟨fun _ => 0, fun a b => 1 + max a b⟩

def Lens.leaves : Lens Nat :=
  ⟨fun _ => 1, (· + ·)⟩

def Lens.id' : Lens Raw :=
  ⟨Raw.object, Raw.relation⟩

theorem lens_depth_eq_raw_depth (x : Raw) :
    Lens.depth.view x = x.depth := by
  induction x with
  | object _ => rfl
  | relation a b iha ihb =>
      show 1 + max (Lens.depth.view a) (Lens.depth.view b) = 1 + max a.depth b.depth
      rw [iha, ihb]

-- ═══ Section 9: Kernel (equivalence) ═══

def Lens.equiv {α : Type} (L : Lens α) (x y : Raw) : Prop :=
  L.view x = L.view y

theorem Lens.equiv_refl {α : Type} (L : Lens α) (x : Raw) :
    L.equiv x x := rfl

theorem Lens.equiv_symm {α : Type} (L : Lens α) {x y : Raw} :
    L.equiv x y → L.equiv y x := Eq.symm

theorem Lens.equiv_trans {α : Type} (L : Lens α) {x y z : Raw} :
    L.equiv x y → L.equiv y z → L.equiv x z := Eq.trans

-- ═══ Section 10: Pair ═══

def Lens.pair {α β : Type} (L : Lens α) (M : Lens β) :
    Lens (α × β) where
  objValue i := (L.objValue i, M.objValue i)
  combine p q := (L.combine p.1 q.1, M.combine p.2 q.2)

theorem pair_view {α β : Type} (L : Lens α) (M : Lens β) (x : Raw) :
    (L.pair M).view x = (L.view x, M.view x) := by
  induction x with
  | object _ => rfl
  | relation a b iha ihb =>
      show (L.combine ((L.pair M).view a).1 ((L.pair M).view b).1,
            M.combine ((L.pair M).view a).2 ((L.pair M).view b).2)
           = (L.combine (L.view a) (L.view b), M.combine (M.view a) (M.view b))
      rw [iha, ihb]

-- ═══ Section 11: Refines ═══

def Lens.refines {α β : Type} (L : Lens α) (M : Lens β) : Prop :=
  ∀ x y : Raw, L.equiv x y → M.equiv x y

theorem Lens.refines_refl {α : Type} (L : Lens α) : L.refines L :=
  fun _ _ h => h

theorem Lens.refines_trans {α β γ : Type}
    {L : Lens α} {M : Lens β} {N : Lens γ} :
    L.refines M → M.refines N → L.refines N :=
  fun h1 h2 x y h => h2 x y (h1 x y h)

-- ═══ Section 12: Third object (derived, not axiomatic) ═══

/-- The two base objects. -/
def o0 : Raw := .object 0
def o1 : Raw := .object 1

/-- The third entity: the relation object produced from the two base objects.
    This is a *consequence* of the axiom, not a postulate. -/
def o01 : Raw := .relation o0 o1

/-- Three distinct Reachable objects exist: `o0`, `o1`, `o01`.
    Thus "three" is derived from the axiom's "two" plus one application of
    `relation`, rather than being hardwired into the base index type. -/
theorem three_objects_exist :
    Reachable o0 ∧ Reachable o1 ∧ Reachable o01 ∧
    o0 ≠ o1 ∧ o0 ≠ o01 ∧ o1 ≠ o01 := by
  refine ⟨.base 0, .base 1, .step (.base 0) (.base 1) ?_, ?_, ?_, ?_⟩ <;> decide

example : Reachable o0 := .base 0
example : Reachable o01 := .step (.base 0) (.base 1) (by decide)
example : ¬ Reachable (.relation o0 o0) :=
  no_self_relation_reachable o0

-- ═══ End of formal foundation ═══
