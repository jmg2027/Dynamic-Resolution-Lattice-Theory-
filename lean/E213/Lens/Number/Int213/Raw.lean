import E213.Theory.Raw.API
import E213.Lens.LensCore
import E213.Meta.Int213.Core
import E213.Lens.Number.Nat213.Tower.NatPairToInt

/-!
# Lens.Number.Int213.Raw — ℤ seen as Raw under a signed lens

**The point**: Nat213.Raw is the `⟨1, 1, +⟩` view of Raw, and Int213.Raw is
the `⟨1, -1, +⟩` view of Raw.  Same Raw, different lens.

  - `Lens.leaves = ⟨1, 1, +⟩ : Lens Nat` — atoms a, b are both +1, combine is
    addition.  view = leaves count.  Lens.equiv = "same leaves count".
    The meaning of Nat213.Raw.
  - `signedLens = ⟨1, -1, +⟩ : Lens Int` — atom a is +1, atom b is -1,
    combine is addition.  view = signed leaves net.  Lens.equiv = "same
    signedNet".  **The Int213 of this file**.

**No new type is introduced**.  The carrier is just Raw.  "ℤ" is emergent in
the codomain (Lean Int); on the Raw side it is implicit as a quotient —
handled by `Lens.equiv`.  Parallel: the leaves-quotient of Nat213.Raw is also
many-to-one (e.g. slash a b and slash b a are equal after canonicalization via
cmp; slash a (slash a b) and slash b (slash a (slash a b)) etc. differ in
leaves but are normalized within the same ℕ₊ quotient).

**Origin of 0**: the 213 axioms have no nullary atom, but the ⟨1, -1, +⟩
codomain is ℤ, so 0 is an algebraic result in the codomain (1 + -1 = 0).  The
corresponding Raw side: there are infinitely many Raws with `value r = 0` — the
minimal-leaves canonical is `slash a b`.  parallel: isomorphic to the way a
Nat213 numeral n is the canonical representative of leaves count n+1.

**Negation lens**: Raw.swap.  `Raw.fold_signed_swap` (Theory/Raw/
Signed.lean) already proves `value (swap r) = - value r`.

∅-axiom; 0 use of Mathlib/Classical.
-/

namespace E213.Lens.Number.Int213.Raw

open E213.Theory
open E213.Lens

/-! ## Signed lens — the ℤ view of Raw -/

/-- ℤ-valued signed lens — atom a = +1, atom b = -1, combine = (·+·). -/
def signedLens : Lens Int := ⟨1, -1, (· + ·)⟩

/-- The signed integer view of Raw (signedLens.view). -/
def value (r : Raw) : Int := signedLens.view r

theorem value_a : value Raw.a = 1 := rfl
theorem value_b : value Raw.b = -1 := rfl

/-- signed-add compatibility of `slash`: since combine is Int's + and add_comm
    is symmetric, `Raw.fold_slash` applies directly. -/
theorem value_slash (x y : Raw) (h : x ≠ y) :
    value (Raw.slash x y h) = value x + value y :=
  Raw.fold_slash (1 : Int) (-1) (· + ·)
    (fun u v => E213.Meta.Int213.add_comm u v) x y h

/-! ## Negation via Raw.swap

Tree-level `Tree.fold_signed_swap` and Raw-level `Raw.fold_signed_swap`
already prove: in the codomain of signedLens, swap acts as `-·`. -/

/-- Sign inversion — Raw.swap.  (from the lens view) `value (neg r) = -value r`. -/
def neg : Raw → Raw := Raw.swap

theorem value_neg (r : Raw) : value (neg r) = -value r :=
  Raw.fold_signed_swap r

theorem neg_neg (r : Raw) : neg (neg r) = r := Raw.swap_swap r

theorem neg_a : neg Raw.a = Raw.b := Raw.swap_a
theorem neg_b : neg Raw.b = Raw.a := Raw.swap_b

/-! ## Lens-induced equality (the ℤ-equivalence on Raw)

Two Raws are "the same integer" iff their `signedLens.view` are equal.  An
instance of `Lens.equiv` (LensCore). -/

/-- Int213-equality on Raw: signedLens.view agree. -/
def equiv (x y : Raw) : Prop := signedLens.equiv x y

theorem equiv_iff (x y : Raw) : equiv x y ↔ value x = value y := Iff.rfl

theorem equiv_refl (r : Raw) : equiv r r := signedLens.equiv_refl r
theorem equiv_symm {x y : Raw} : equiv x y → equiv y x := signedLens.equiv_symm
theorem equiv_trans {x y z : Raw} : equiv x y → equiv y z → equiv x z :=
  signedLens.equiv_trans

/-- `neg` preserves lens-equivalence — neg is injective (via Raw.swap_swap). -/
theorem equiv_neg {x y : Raw} (h : equiv x y) : equiv (neg x) (neg y) := by
  have h' : value x = value y := h
  show value (neg x) = value (neg y)
  rw [value_neg, value_neg, h']

/-! ## Canonical Raw representatives — Method A for ℤ

Parallel to Nat213.Raw's `one = Raw.a`, `numeral n = succ chain`.
Here we expose only the minimal-leaves canonical (chain extension can be
added). -/

/-- `Raw.a ≠ Raw.b` — decidable. -/
private theorem a_ne_b : Raw.a ≠ Raw.b := by decide

/-- The 0 of ℤ — canonical Raw representative `slash a b`.  signedLens.view = 0. -/
def zero : Raw := Raw.slash Raw.a Raw.b a_ne_b

theorem value_zero : value zero = 0 := rfl

/-- The +1 of ℤ — canonical Raw representative `Raw.a`. -/
def one : Raw := Raw.a

theorem value_one : value one = 1 := rfl

/-- The -1 of ℤ — canonical Raw representative `Raw.b`. -/
def negOne : Raw := Raw.b

theorem value_negOne : value negOne = -1 := rfl

theorem neg_one : neg one = negOne := Raw.swap_a
theorem neg_negOne : neg negOne = one := Raw.swap_b

/-- `zero` is a fixed point of `neg` — 0 = -0. -/
theorem neg_zero : equiv (neg zero) zero := by
  show value (neg zero) = value zero
  rw [value_neg, value_zero]
  rfl

/-! ## Pair lens — orthogonal-axis decomposition of signedLens

Decompose the codomain `Int` of `signedLens = ⟨1, -1, +⟩ : Lens Int` into two
ℕ-axes: accumulating a-count and b-count separately gives `Lens (ℕ × ℕ)`.
Projecting the view of this pair lens through `Tower.NatPairToInt.npairToInt`
agrees with signedLens — **`signedLens = npairToInt ∘ pairLens`**. -/

/-- Component-wise pair add. -/
private def pairCombine (p q : Nat × Nat) : Nat × Nat := (p.1 + q.1, p.2 + q.2)

/-- pairLens — atom decomposition of Raw.  atom a = (1, 0), atom b = (0, 1),
    combine = component-wise +.  view = (a-count, b-count). -/
def pairLens : Lens (Nat × Nat) := ⟨(1, 0), (0, 1), pairCombine⟩

/-- The atom-decomposition pair of Raw (pairLens.view). -/
def pairCount (r : Raw) : Nat × Nat := pairLens.view r

theorem pairCount_a : pairCount Raw.a = (1, 0) := rfl
theorem pairCount_b : pairCount Raw.b = (0, 1) := rfl

/-- pairCombine is commutative — component-wise Nat.add_comm. -/
private theorem pairCombine_comm (p q : Nat × Nat) :
    pairCombine p q = pairCombine q p := by
  show (p.1 + q.1, p.2 + q.2) = (q.1 + p.1, q.2 + p.2)
  rw [Nat.add_comm p.1 q.1, Nat.add_comm p.2 q.2]

/-- slash compatibility of pairLens: view (slash x y) = combine (view x) (view y). -/
theorem pairCount_slash (x y : Raw) (h : x ≠ y) :
    pairCount (Raw.slash x y h) = pairCombine (pairCount x) (pairCount y) :=
  Raw.fold_slash (1, 0) (0, 1) pairCombine pairCombine_comm x y h

/-! ### Factoring: signedLens = npairToInt ∘ pairLens

The keystone `Meta.Int213.subNatNat_add_subNatNat` already proves, ∅-axiom,
`subNatNat a b + subNatNat c d = subNatNat (a+c) (b+d)`; the factoring closes
with a one-line Tree induction. -/

open E213.Term.Internal (Tree)

/-- Tree-level factoring (private; the Raw-level lift is below). -/
private theorem tree_signedLens_factor (t : Tree) :
    Tree.fold (1 : Int) (-1) (· + ·) t
      = Int.subNatNat
          (Tree.fold (1, 0) (0, 1) pairCombine t).1
          (Tree.fold (1, 0) (0, 1) pairCombine t).2 := by
  induction t with
  | a => rfl
  | b => rfl
  | slash x y ihx ihy =>
      show Tree.fold (1 : Int) (-1) (· + ·) x
           + Tree.fold (1 : Int) (-1) (· + ·) y
         = Int.subNatNat
             ((Tree.fold (1, 0) (0, 1) pairCombine x).1
              + (Tree.fold (1, 0) (0, 1) pairCombine y).1)
             ((Tree.fold (1, 0) (0, 1) pairCombine x).2
              + (Tree.fold (1, 0) (0, 1) pairCombine y).2)
      rw [ihx, ihy]
      exact E213.Meta.Int213.subNatNat_add_subNatNat _ _ _ _

/-- ★ Factoring: signedLens.view agrees with projecting pairLens.view through
    `npairToInt` (the morphism of Tower).  That is, Raw → ℤ commutes as
    Raw → ℕ × ℕ → ℤ. -/
theorem signedLens_factors_through_pairLens (r : Raw) :
    value r = E213.Lens.Number.Nat213.Tower.NatPairToInt.npairToInt (pairCount r) :=
  tree_signedLens_factor r.val

/-- pairLens refines signedLens — same pairCount implies same signed
    value.  A direct corollary of the Factoring. -/
theorem pairLens_refines_signedLens : pairLens.refines signedLens := by
  intro x y h
  show value x = value y
  rw [signedLens_factors_through_pairLens x,
      signedLens_factors_through_pairLens y]
  exact congrArg _ h

end E213.Lens.Number.Int213.Raw
