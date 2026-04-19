/-!
# 213: Formal Foundation

## Axiom (single primitive)

Given two objects, there exists a relation object between them.

## Formal statement

`Raw` is an inductive type with two constructors:
- `object : Fin 3 → Raw`: base objects (labeled by Fin 3).
- `relation : Raw → Raw → Raw`: binary relation object between two Raw.

The axiom's "two" is captured by `Reachable` derivation:
a relation object is Reachable only from two distinct Reachable objects.

## Consequences

- Identity (=) is not a primitive.
- Apartness (≠) is used only as Lean's technical encoding of "two".
- `relation x x` (same-input case) is not Reachable (axiom scope).
-/

-- ═══ Section 1: Primitive Type ═══

inductive Raw where
  | object   : Fin 3 → Raw
  | relation : Raw → Raw → Raw
  deriving DecidableEq, Repr

-- ═══ Section 2: Reachable (axiom derivation) ═══

inductive Reachable : Raw → Prop where
  | base : (i : Fin 3) → Reachable (.object i)
  | step : Reachable x → Reachable y → x ≠ y →
           Reachable (.relation x y)

-- ═══ Section 3: Well-formedness ═══

def Raw.wellFormed : Raw → Prop
  | .object _     => True
  | .relation x y => x ≠ y ∧ x.wellFormed ∧ y.wellFormed

instance : DecidablePred Raw.wellFormed := by
  intro x
  induction x with
  | object _ => exact isTrue trivial
  | relation a b iha ihb =>
    simp [Raw.wellFormed]
    exact instDecidableAnd

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

theorem relation_depth_gt {x y : Raw} (h : x ≠ y) :
    (Raw.relation x y).depth > x.depth := by
  simp [Raw.depth]; omega

-- ═══ Section 7: Lens ═══

structure Lens (α : Type) where
  objValue : Fin 3 → α
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
  | relation a b iha ihb => simp [Lens.view, Lens.depth, Raw.depth, iha, ihb]

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
         = _
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

-- ═══ Section 12: Examples ═══

def o0 : Raw := .object 0
def o1 : Raw := .object 1
def o2 : Raw := .object 2

example : Reachable o0 := .base 0
example : Reachable (.relation o0 o1) :=
  .step (.base 0) (.base 1) (by decide)
example : ¬ Reachable (.relation o0 o0) :=
  no_self_relation_reachable o0

-- ═══ End of formal foundation ═══
