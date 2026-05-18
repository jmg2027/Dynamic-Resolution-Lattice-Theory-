import E213.Theory.Raw.API
import E213.Lens.LensCore

/-!
# Lens.Number.Nat213.Core — Lens-derived ℕ₊ type

**Phase 1 of the lens-strict refactor**: encapsulate the image of
`Lens.leaves = ⟨1, 1, +⟩ : Lens Nat` as a named type.

`Lens.leaves.view : Raw → Nat` 의 image 가 정확히 `{ n : Nat // 1 ≤ n }`
(모든 Raw 는 leaves ≥ 1).  이 subtype 을 `Nat213` 으로 명명.
Downstream 은 `Nat213` 을 abstract ℕ₊ type 으로 사용; underneath
는 `Lens.leaves.view → Raw.fold → Tree.fold` 가 호출됨.

이게 Lens-coherent abstraction: lens 의 image-with-closure 가 type.

∅-axiom; Mathlib/Classical 사용 0.
-/

namespace E213.Lens.Number

open E213.Theory
open E213.Lens
open E213.Term.Internal (Tree)

/-- 213-native ℕ₊ — `Lens.leaves` 의 codomain image subtype. -/
def Nat213 : Type := { n : Nat // 1 ≤ n }

namespace Nat213

/-- 내부 Nat 값 추출. -/
def toNat (n : Nat213) : Nat := n.val

theorem toNat_ge_one (n : Nat213) : 1 ≤ n.toNat := n.property

/-- ℕ₊ 의 1. -/
def one : Nat213 := ⟨1, Nat.le_refl 1⟩

theorem toNat_one : Nat213.one.toNat = 1 := rfl

/-- successor — 항상 n+1 ≥ 1. -/
def succ (n : Nat213) : Nat213 :=
  ⟨n.val + 1, Nat.le_succ_of_le n.property⟩

theorem toNat_succ (n : Nat213) : n.succ.toNat = n.toNat + 1 := rfl

/-- 덧셈 — Nat 덧셈 lift, 1 ≤ 는 left arg 의 보존으로. -/
def add (m n : Nat213) : Nat213 :=
  ⟨m.val + n.val, Nat.le_trans m.property (Nat.le_add_right _ _)⟩

theorem toNat_add (m n : Nat213) : (m.add n).toNat = m.toNat + n.toNat := rfl

/-- 곱셈 — Nat 곱셈 lift, 1 ≤ 는 1 * 1 ≤ m * n. -/
def mul (m n : Nat213) : Nat213 :=
  ⟨m.val * n.val, Nat.mul_le_mul m.property n.property⟩

theorem toNat_mul (m n : Nat213) : (m.mul n).toNat = m.toNat * n.toNat := rfl

end Nat213

/-! ### Lens.leaves view 를 Nat213 으로 lift -/

/-- 모든 Raw 의 leaves count ≥ 1 (atom 에서 1 시작, slash 가 더해짐). -/
theorem leaves_view_ge_one (r : Raw) : 1 ≤ Lens.leaves.view r := by
  show 1 ≤ Raw.fold 1 1 (· + ·) r
  show 1 ≤ Tree.fold (1 : Nat) 1 (· + ·) r.val
  induction r.val with
  | a => exact Nat.le_refl 1
  | b => exact Nat.le_refl 1
  | slash x y ihx _ =>
      show 1 ≤ Tree.fold 1 1 (· + ·) x + Tree.fold 1 1 (· + ·) y
      exact Nat.le_trans ihx (Nat.le_add_right _ _)

/-- Raw → Nat213 — Lens.leaves.view 를 image subtype 으로 lift. -/
def Raw.toNat213 (r : Raw) : Nat213 :=
  ⟨Lens.leaves.view r, leaves_view_ge_one r⟩

theorem Raw.toNat213_a : (Raw.toNat213 Raw.a).toNat = 1 := rfl
theorem Raw.toNat213_b : (Raw.toNat213 Raw.b).toNat = 1 := rfl

/-- slash 의 lens 호환: `slash x y` 의 view = view x + view y. -/
theorem Raw.toNat213_slash (x y : Raw) (h : x ≠ y) :
    (Raw.toNat213 (Raw.slash x y h)).toNat
      = (Raw.toNat213 x).toNat + (Raw.toNat213 y).toNat :=
  Raw.fold_slash 1 1 (· + ·) (fun u v => Nat.add_comm u v) x y h

end E213.Lens.Number
