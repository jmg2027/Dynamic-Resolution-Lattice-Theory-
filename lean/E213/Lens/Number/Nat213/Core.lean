import E213.Theory.Raw.API
import E213.Lens.LensCore

/-!
# Lens.Number.Nat213.Core — Lens-derived ℕ₊ type

Encapsulate the image of `Lens.leaves = ⟨1, 1, +⟩ : Lens Nat` as
a named type.  Originally the Phase 1 step of the lens-strict
refactor (Option C of the lens-emergence roadmap, commit
`ced56bef`); the full refactor has since landed (Option
C in `9efd8263`) — `Raw.lean` no longer carries arithmetic, and
`Chain.lean` provides the dual Raw-subtype carrier with Nat-routed
operations.

The image of `Lens.leaves.view : Raw → Nat` is exactly `{ n : Nat // 1 ≤ n }`
(every Raw has leaves ≥ 1).  We name this subtype `Nat213`.
Downstream uses `Nat213` as an abstract ℕ₊ type; underneath,
`Lens.leaves.view → Raw.fold → Tree.fold` is invoked.

This is the Lens-coherent abstraction: the lens's image-with-closure is the type.

∅-axiom; 0 use of Mathlib/Classical.
-/

namespace E213.Lens.Number

open E213.Theory
open E213.Lens
open E213.Term.Internal (Tree)

/-- 213-native ℕ₊ — the codomain image subtype of `Lens.leaves`. -/
def Nat213 : Type := { n : Nat // 1 ≤ n }

namespace Nat213

/-- Extract the internal Nat value. -/
def toNat (n : Nat213) : Nat := n.val

theorem toNat_ge_one (n : Nat213) : 1 ≤ n.toNat := n.property

/-- The 1 of ℕ₊. -/
def one : Nat213 := ⟨1, Nat.le_refl 1⟩

theorem toNat_one : Nat213.one.toNat = 1 := rfl

/-- successor — always n+1 ≥ 1. -/
def succ (n : Nat213) : Nat213 :=
  ⟨n.val + 1, Nat.le_succ_of_le n.property⟩

theorem toNat_succ (n : Nat213) : n.succ.toNat = n.toNat + 1 := rfl

/-- Addition — a lift of Nat addition; 1 ≤ via preservation from the left arg. -/
def add (m n : Nat213) : Nat213 :=
  ⟨m.val + n.val, Nat.le_trans m.property (Nat.le_add_right _ _)⟩

theorem toNat_add (m n : Nat213) : (m.add n).toNat = m.toNat + n.toNat := rfl

/-- Multiplication — a lift of Nat multiplication; 1 ≤ via 1 * 1 ≤ m * n. -/
def mul (m n : Nat213) : Nat213 :=
  ⟨m.val * n.val, Nat.mul_le_mul m.property n.property⟩

theorem toNat_mul (m n : Nat213) : (m.mul n).toNat = m.toNat * n.toNat := rfl

end Nat213

/-! ### Lifting the Lens.leaves view to Nat213 -/

/-- The leaves count of every Raw is ≥ 1 (starts at 1 from an atom, slash adds). -/
theorem leaves_view_ge_one (r : Raw) : 1 ≤ Lens.leaves.view r := by
  show 1 ≤ Raw.fold 1 1 (· + ·) r
  show 1 ≤ Tree.fold (1 : Nat) 1 (· + ·) r.val
  induction r.val with
  | a => exact Nat.le_refl 1
  | b => exact Nat.le_refl 1
  | slash x y ihx _ =>
      show 1 ≤ Tree.fold 1 1 (· + ·) x + Tree.fold 1 1 (· + ·) y
      exact Nat.le_trans ihx (Nat.le_add_right _ _)

/-- Raw → Nat213 — lift Lens.leaves.view into the image subtype. -/
def Raw.toNat213 (r : Raw) : Nat213 :=
  ⟨Lens.leaves.view r, leaves_view_ge_one r⟩

theorem Raw.toNat213_a : (Raw.toNat213 Raw.a).toNat = 1 := rfl
theorem Raw.toNat213_b : (Raw.toNat213 Raw.b).toNat = 1 := rfl

/-- lens compatibility of slash: the view of `slash x y` = view x + view y. -/
theorem Raw.toNat213_slash (x y : Raw) (h : x ≠ y) :
    (Raw.toNat213 (Raw.slash x y h)).toNat
      = (Raw.toNat213 x).toNat + (Raw.toNat213 y).toNat :=
  Raw.fold_slash 1 1 (· + ·) (fun u v => Nat.add_comm u v) x y h

end E213.Lens.Number
