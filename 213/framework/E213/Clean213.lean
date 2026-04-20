/-!
# 213: Firmware (3-line axiom)

## The axiom

1. Something exists.
2. To know what it is, another something is required.
3. That other something is also a something.

Clauses (1)-(2) name an existing "something" and a distinguishing
partner; (3) closes the rule recursively — the distinguishing
partner is again a something, so the rule applies to it in turn.

## Formal statement

```
inductive Raw where
  | a     : Raw               -- a first something
  | b     : Raw               -- its distinguishing partner
  | slash : Raw → Raw → Raw   -- the act of distinguishing
```

The axiom supplies **no** equality, inequality, ordering, or any
means of identifying subtrees. These arise only at the Lens layer
(the Hypervisor, §4), where each Lens's kernel provides its own
notion of "same" — Lens-dependent by design.

Terms of `Raw` are generated freely by the three clauses. In
particular, `slash x x` is a valid term for any `x`; whether that
term means anything is a Lens-level question.
-/

-- ═══ Firmware: the inductive type ═══

inductive Raw where
  | a     : Raw
  | b     : Raw
  | slash : Raw → Raw → Raw
  deriving DecidableEq, Repr

-- ═══ Depth (purely structural, no equality needed) ═══

def Raw.depth : Raw → Nat
  | .a         => 0
  | .b         => 0
  | .slash x y => 1 + max x.depth y.depth

theorem Raw.slash_depth_gt_left {x y : Raw} :
    (Raw.slash x y).depth > x.depth := by
  simp [Raw.depth]; omega

-- ═══ Hypervisor: the Lens layer (§4) ═══

structure Lens (α : Type) where
  base_a  : α
  base_b  : α
  combine : α → α → α

def Lens.view {α : Type} (L : Lens α) : Raw → α
  | .a         => L.base_a
  | .b         => L.base_b
  | .slash x y => L.combine (L.view x) (L.view y)

-- Kernel equivalence: equality derived from a Lens, not primitive.
def Lens.equiv {α : Type} (L : Lens α) (x y : Raw) : Prop :=
  L.view x = L.view y

theorem Lens.equiv_refl {α} (L : Lens α) (x : Raw) : L.equiv x x := rfl

theorem Lens.equiv_symm {α} (L : Lens α) {x y : Raw} :
    L.equiv x y → L.equiv y x := Eq.symm

theorem Lens.equiv_trans {α} (L : Lens α) {x y z : Raw} :
    L.equiv x y → L.equiv y z → L.equiv x z := Eq.trans

-- Pair of lenses: product view.
def Lens.pair {α β : Type} (L : Lens α) (M : Lens β) : Lens (α × β) where
  base_a  := (L.base_a, M.base_a)
  base_b  := (L.base_b, M.base_b)
  combine p q := (L.combine p.1 q.1, M.combine p.2 q.2)

theorem pair_view {α β : Type} (L : Lens α) (M : Lens β) (x : Raw) :
    (L.pair M).view x = (L.view x, M.view x) := by
  induction x with
  | a => rfl
  | b => rfl
  | slash x y ihx ihy =>
      show (L.combine ((L.pair M).view x).1 ((L.pair M).view y).1,
            M.combine ((L.pair M).view x).2 ((L.pair M).view y).2)
           = (L.combine (L.view x) (L.view y), M.combine (M.view x) (M.view y))
      rw [ihx, ihy]

-- Refines: L refines M iff L's kernel is finer than M's.
def Lens.refines {α β : Type} (L : Lens α) (M : Lens β) : Prop :=
  ∀ x y : Raw, L.equiv x y → M.equiv x y

theorem Lens.refines_refl {α} (L : Lens α) : L.refines L := fun _ _ h => h

theorem Lens.refines_trans {α β γ} {L : Lens α} {M : Lens β} {N : Lens γ} :
    L.refines M → M.refines N → L.refines N :=
  fun h1 h2 x y h => h2 x y (h1 x y h)

-- Canonical Lenses.

/-- Depth Lens: recovers the depth function. -/
def Lens.depth : Lens Nat :=
  ⟨0, 0, fun p q => 1 + max p q⟩

/-- Leaves Lens: counts the base-object occurrences. -/
def Lens.leaves : Lens Nat :=
  ⟨1, 1, (· + ·)⟩

/-- Identity Lens: tautological. -/
def Lens.id' : Lens Raw :=
  ⟨.a, .b, .slash⟩

theorem lens_depth_eq_raw_depth (x : Raw) :
    Lens.depth.view x = x.depth := by
  induction x with
  | a => rfl
  | b => rfl
  | slash p q ihp ihq =>
      show 1 + max (Lens.depth.view p) (Lens.depth.view q)
           = 1 + max p.depth q.depth
      rw [ihp, ihq]

-- The third entity (axiom clause 3): a, b, and a/b. "Three" is
-- derived from the axiom, not postulated.

example : Raw := .slash .a .b           -- the third entity exists
example : (Raw.slash .a .b).depth = 1 := rfl
