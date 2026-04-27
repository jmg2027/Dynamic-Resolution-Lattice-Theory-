import E213.Hypervisor.Lens
import E213.Meta.ParityLens
import E213.Meta.BoolLens
import E213.Research.F9Lens

/-!
# Research.DiagonalClassification: combine 의 diagonal 거동 분류

Note 34 §3 Q34.1 의 Lean 화.

각 Lens 의 `combine v v` 함수 (diagonal 값) 를 `sq L : α → α`
로 부각.  네 거동:

- **Collapse** (parityLens): `sq v = e` (상수).  α 의 한 점 e
  으로 접힘.  xor 의 경우 e = false = identity (2-torsion).
- **Idempotent** (boolAndLens, boolOrLens): `sq v = v` (항등).
  semilattice 연산의 특성.
- **Escalate** (Lens.leaves): `sq v = v + v` (배가).  commutative
  group 에서 self-doubling.
- **Multiply** (f9Lens): `sq v = v * v` (제곱).  ring multiplication.

Collapse + Idempotent 동시 성립은 |α| = 1 강제.  상호 배타적.
-/

namespace E213.Research.DiagonalClassification

open E213.Firmware E213.Hypervisor

/-- **Squaring function** — Lens 의 diagonal 로 유도되는 α → α. -/
def sq {α : Type} (L : Lens α) (v : α) : α := L.combine v v

/-- **Collapse** — diagonal 이 한 점 `e` 로. -/
def Collapse {α : Type} (L : Lens α) (e : α) : Prop :=
  ∀ v : α, L.combine v v = e

/-- **Idempotent** — diagonal 이 항등. -/
def Idempotent {α : Type} (L : Lens α) : Prop :=
  ∀ v : α, L.combine v v = v

/-! ## §1. 분류의 상호 배타성 -/

/-- Collapse 와 Idempotent 동시 성립 → α 는 실질 단일점
    (모든 v 가 e 와 같음). -/
theorem collapse_idempotent_trivial {α : Type} (L : Lens α) (e : α)
    (hC : Collapse L e) (hI : Idempotent L) :
    ∀ v : α, v = e := by
  intro v
  have h1 : L.combine v v = e := hC v
  have h2 : L.combine v v = v := hI v
  exact h2.symm.trans h1

end E213.Research.DiagonalClassification

namespace E213.Research.DiagonalClassification

open E213.Firmware E213.Hypervisor E213.Meta

/-! ## §2. Bool Lens 들의 분류 -/

/-- parityLens 는 Collapse (e = false). -/
theorem parityLens_collapse : Collapse parityLens false := by
  intro v; cases v <;> rfl

/-- boolAndLens 는 Idempotent. -/
theorem boolAndLens_idempotent : Idempotent boolAndLens := by
  intro v; cases v <;> rfl

/-- boolOrLens 는 Idempotent. -/
theorem boolOrLens_idempotent : Idempotent boolOrLens := by
  intro v; cases v <;> rfl

end E213.Research.DiagonalClassification

namespace E213.Research.DiagonalClassification

open E213.Firmware E213.Hypervisor

/-! ## §3. Nat Lens 의 분류 — Escalate -/

/-- Lens.leaves 는 Escalate: sq v = v + v. -/
theorem leaves_escalate (v : Nat) :
    sq Lens.leaves v = v + v := rfl

/-- Lens.leaves 는 Idempotent 가 아님 (v = 1 반례). -/
theorem leaves_not_idempotent : ¬ Idempotent Lens.leaves := by
  intro hI
  have h : (1 : Nat) + 1 = 1 := hI 1
  cases h

end E213.Research.DiagonalClassification

namespace E213.Research.DiagonalClassification

open E213.Firmware E213.Hypervisor E213.Research.F9Lens

/-! ## §4. F9 Lens 의 분류 — Multiply -/

/-- f9Lens 는 Multiply: sq v = F9.mul v v. -/
theorem f9Lens_multiply (v : F9) :
    sq f9Lens v = F9.mul v v := rfl

/-- f9Lens 는 Idempotent 가 아님 (i² = -1 ≠ i). -/
theorem f9Lens_not_idempotent : ¬ Idempotent f9Lens := by
  intro hI
  have h : F9.mul F9.i F9.i = F9.i := hI F9.i
  have hne : F9.mul F9.i F9.i ≠ F9.i := by decide
  exact hne h

/-- f9Lens 는 어떤 e 에 대해서도 Collapse 가 아님 (1² ≠ i²). -/
theorem f9Lens_not_collapse : ¬ ∃ e : F9, Collapse f9Lens e := by
  intro ⟨e, hC⟩
  have h1 : F9.mul F9.one F9.one = e := hC F9.one
  have h2 : F9.mul F9.i F9.i = e := hC F9.i
  have hne : F9.mul F9.one F9.one ≠ F9.mul F9.i F9.i := by decide
  exact hne (h1.trans h2.symm)

end E213.Research.DiagonalClassification
