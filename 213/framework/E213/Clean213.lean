/-!
# 213: Firmware — free commutative magma (no self-operation)

## Axiom (3 clauses)

1. *Something exists.*
2. *To know what it is, another something is required.*  (⟹ anti-reflexive: no `x/x`)
3. *That other something is also a something.*  (⟹ recursion;
   "between" is directionless ⟹ symmetric: `x/y = y/x`)

## Target and implementation

The axiom gives a **free commutative magma on 2 generators with no
fixed points** — the unique closure under `slash` satisfying
anti-reflexivity and symmetry. This quotient structure is the
minimal model of the axiom clauses.

**Lean is not a set theory and has no primitive quotients without
Mathlib.** We therefore *emulate* the intended structure by a
subtype of a free (ordered) magma restricted to canonical form.
The canonical-form constraint enforces both:
- anti-reflexivity (since `x < y` implies `x ≠ y`);
- symmetry collapse (each unordered pair has a unique canonical
  ordered representative).

The ordering itself is an *implementation artifact*: it does not
exist in the axiom. Any total order on the raw tree would do; we
use a structural one. No set-theoretic primitive (ZFC-style
`{x,y}`, Mathlib `Multiset`, etc.) is imported; the entire
construction lives inside Lean 4 core.

## Layering

- **Firmware (§1).** `Tree` (free ordered magma), `canonical`
  predicate, `Raw := subtype of canonical Tree`. Encodes the
  axiom under the above emulation.
- **Hypervisor (§4+).** `Lens` over `Raw`. Equality/inequality on
  Raw is recovered at the Lens level as kernel-equivalence; not a
  primitive.
-/

-- ═══ Internal: free ordered magma (pre-canonical) ═══

inductive Tree : Type
  | a     : Tree
  | b     : Tree
  | slash : Tree → Tree → Tree
  deriving DecidableEq, Repr

-- ═══ Total order on Tree (implementation scaffolding) ═══

/-- Lexicographic structural comparison.  `a < b < slash _ _`, and
    `slash x₁ y₁ < slash x₂ y₂` iff `(x₁, y₁) < (x₂, y₂)` lex. -/
def Tree.cmp : Tree → Tree → Ordering
  | .a,         .a         => .eq
  | .a,         .b         => .lt
  | .a,         .slash _ _ => .lt
  | .b,         .a         => .gt
  | .b,         .b         => .eq
  | .b,         .slash _ _ => .lt
  | .slash _ _, .a         => .gt
  | .slash _ _, .b         => .gt
  | .slash x₁ y₁, .slash x₂ y₂ =>
      match Tree.cmp x₁ x₂ with
      | .eq => Tree.cmp y₁ y₂
      | ord => ord

/-- A Tree is *canonical* iff every `slash` node has strictly
    ordered children (in particular, no self-slash). -/
def Tree.canonical : Tree → Bool
  | .a         => true
  | .b         => true
  | .slash x y =>
      x.canonical && y.canonical &&
      (match Tree.cmp x y with | .lt => true | _ => false)

-- ═══ Raw: the canonical subtype ═══

def Raw : Type := { t : Tree // t.canonical = true }

instance : DecidableEq Raw := fun ⟨x, _⟩ ⟨y, _⟩ =>
  match decEq x y with
  | .isTrue h  => .isTrue (Subtype.ext h)
  | .isFalse h => .isFalse (fun e => h (congrArg Subtype.val e))

-- The two base Raw terms (axiom clause 1 + (3)'s "another something").

def Raw.a : Raw := ⟨.a, rfl⟩
def Raw.b : Raw := ⟨.b, rfl⟩

-- Specific constructions via `decide` (computation of canonical predicate).

/-- The third entity: the unique Level-1 closure `a/b`. -/
def Raw.ab : Raw := ⟨.slash .a .b, by decide⟩

/-- Level-2 additions: `a/(a/b)` and `b/(a/b)`. -/
def Raw.a_ab : Raw := ⟨.slash .a (.slash .a .b), by decide⟩
def Raw.b_ab : Raw := ⟨.slash .b (.slash .a .b), by decide⟩

example : (Raw.ab).val.canonical = true := rfl
example : (Raw.a_ab).val.canonical = true := rfl
example : (Raw.b_ab).val.canonical = true := rfl

-- The five Level-≤2 Raw terms are distinct.
example : Raw.a ≠ Raw.b := by decide
example : Raw.a ≠ Raw.ab := by decide
example : Raw.b ≠ Raw.ab := by decide
example : Raw.ab ≠ Raw.a_ab := by decide
example : Raw.a_ab ≠ Raw.b_ab := by decide

-- ═══ Helper lemmas for the smart slash constructor ═══

theorem Tree.cmp_eq_iff (x y : Tree) : Tree.cmp x y = .eq ↔ x = y := by
  induction x generalizing y with
  | a => cases y <;> simp [Tree.cmp]
  | b => cases y <;> simp [Tree.cmp]
  | slash x₁ y₁ ihx ihy =>
      cases y with
      | a => simp [Tree.cmp]
      | b => simp [Tree.cmp]
      | slash x₂ y₂ =>
          simp only [Tree.cmp]
          constructor
          · intro h
            split at h <;> rename_i hc
            · rw [(ihy y₂).mp h]
              rw [show x₁ = x₂ from (ihx x₂).mp hc]
            all_goals (exfalso; exact Ordering.noConfusion h)
          · intro h
            injection h with hx hy
            rw [hx, hy]
            rw [show Tree.cmp x₂ x₂ = .eq from (ihx x₂).mpr rfl]
            exact (ihy y₂).mpr rfl

theorem Tree.cmp_swap (x y : Tree) :
    Tree.cmp x y = (Tree.cmp y x).swap := by
  induction x generalizing y with
  | a => cases y <;> rfl
  | b => cases y <;> rfl
  | slash x₁ y₁ ihx ihy =>
      cases y with
      | a => rfl
      | b => rfl
      | slash x₂ y₂ =>
          show (match Tree.cmp x₁ x₂ with
                | .eq => Tree.cmp y₁ y₂
                | ord => ord)
              = (match Tree.cmp x₂ x₁ with
                 | .eq => Tree.cmp y₂ y₁
                 | ord => ord).swap
          rw [ihx x₂, ihy y₂]
          cases Tree.cmp x₂ x₁ <;> rfl

theorem Tree.cmp_gt_iff_lt_swap (x y : Tree) :
    Tree.cmp x y = .gt ↔ Tree.cmp y x = .lt := by
  rw [Tree.cmp_swap x y]
  cases Tree.cmp y x <;> simp [Ordering.swap]

-- ═══ Smart slash constructor (the "between" emulation) ═══

/-- Given two **distinct** Raw terms, produce their symmetric
    `slash`: canonical form orders the smaller child first.  The
    ordering is an implementation artifact of the Lean encoding;
    the axiom only requires symmetry, which is ensured because
    every unordered pair has a unique canonical representative. -/
def Raw.slash (x y : Raw) (h : x ≠ y) : Raw :=
  match hc : Tree.cmp x.val y.val with
  | .lt => ⟨.slash x.val y.val, by
            simp [Tree.canonical, x.property, y.property, hc]⟩
  | .gt => ⟨.slash y.val x.val, by
            have hlt : Tree.cmp y.val x.val = .lt :=
              (Tree.cmp_gt_iff_lt_swap x.val y.val).mp hc
            simp [Tree.canonical, y.property, x.property, hlt]⟩
  | .eq => absurd ((Tree.cmp_eq_iff _ _).mp hc)
            (fun e => h (Subtype.ext e))

-- Symmetry at the Raw level.
theorem Raw.slash_comm (x y : Raw) (h : x ≠ y) :
    Raw.slash x y h = Raw.slash y x (Ne.symm h) := by
  unfold Raw.slash
  have hsw : Tree.cmp x.val y.val = (Tree.cmp y.val x.val).swap :=
    Tree.cmp_swap x.val y.val
  split <;> rename_i hc1 <;> split <;> rename_i hc2 <;>
    (first
      | rfl
      | (exfalso
         rw [hc1, hc2] at hsw
         cases hsw))


-- ═══ Hypervisor: Lens layer ═══

/-- A Lens is a codomain `α` with two base values and a binary op.
    The combine is required to be `symmetric` (= commutative) for
    the Lens to respect the axiom's "between" (Raw's symmetry),
    but the structure carries the choice rather than enforcing it:
    asymmetric Lenses can still be defined; they just fail to
    factor through the Raw canonical form. -/
structure Lens (α : Type) where
  base_a  : α
  base_b  : α
  combine : α → α → α

/-- View of a Raw via its underlying Tree. The Tree structure is
    an internal ordered representation; the Lens sees only the
    canonical form. -/
def Lens.viewTree {α : Type} (L : Lens α) : Tree → α
  | .a         => L.base_a
  | .b         => L.base_b
  | .slash x y => L.combine (L.viewTree x) (L.viewTree y)

def Lens.view {α : Type} (L : Lens α) (x : Raw) : α :=
  L.viewTree x.val

-- Sanity checks on the five Level-≤2 constructions.

def Lens.leaves : Lens Nat := ⟨1, 1, (· + ·)⟩

example : Lens.leaves.view Raw.a    = 1 := rfl
example : Lens.leaves.view Raw.b    = 1 := rfl
example : Lens.leaves.view Raw.ab   = 2 := rfl
example : Lens.leaves.view Raw.a_ab = 3 := rfl
example : Lens.leaves.view Raw.b_ab = 3 := rfl

-- Kernel equivalence (lens-derived equality on Raw).
def Lens.equiv {α : Type} (L : Lens α) (x y : Raw) : Prop :=
  L.view x = L.view y

theorem Lens.equiv_refl {α} (L : Lens α) (x : Raw) : L.equiv x x := rfl
theorem Lens.equiv_symm {α} (L : Lens α) {x y : Raw} : L.equiv x y → L.equiv y x := Eq.symm
theorem Lens.equiv_trans {α} (L : Lens α) {x y z : Raw} :
    L.equiv x y → L.equiv y z → L.equiv x z := Eq.trans
