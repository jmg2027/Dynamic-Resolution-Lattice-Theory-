import E213.Hypervisor.Lens
import E213.Meta.ParityLens
import E213.Meta.BoolLens
import E213.Research.Lens.F9

/-!
# Research.DiagonalClassification: Classification of the diagonal behavior of combine

Lean formalization of Note 34 §3 Q34.1.

Highlights the `combine v v` function (diagonal value) of each Lens
as `sq L : α → α`.  Four behaviors:

- **Collapse** (parityLens): `sq v = e` (constant).  Collapsed to
  a single point e in α.  For xor, e = false = identity (2-torsion).
- **Idempotent** (boolAndLens, boolOrLens): `sq v = v` (identity).
  Characteristic of semilattice operations.
- **Escalate** (Lens.leaves): `sq v = v + v` (doubling).
  Self-doubling in a commutative group.
- **Multiply** (f9Lens): `sq v = v * v` (squaring).  Ring multiplication.

Collapse + Idempotent holding simultaneously forces |α| = 1.
Mutually exclusive.
-/

namespace E213.Research.DiagonalClassification

open E213.Firmware E213.Hypervisor

/-- **Squaring function** — the α → α induced by the diagonal of a Lens. -/
def sq {α : Type} (L : Lens α) (v : α) : α := L.combine v v

/-- **Collapse** — diagonal collapses to a single point `e`. -/
def Collapse {α : Type} (L : Lens α) (e : α) : Prop :=
  ∀ v : α, L.combine v v = e

/-- **Idempotent** — diagonal is the identity. -/
def Idempotent {α : Type} (L : Lens α) : Prop :=
  ∀ v : α, L.combine v v = v

/-! ## §1. Mutual exclusivity of classifications -/

/-- Collapse and Idempotent holding simultaneously → α is effectively
    a single point (every v equals e). -/
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

/-! ## §2. Classification of Bool Lenses -/

/-- parityLens is Collapse (e = false). -/
theorem parityLens_collapse : Collapse parityLens false := by
  intro v; cases v <;> rfl

/-- boolAndLens is Idempotent. -/
theorem boolAndLens_idempotent : Idempotent boolAndLens := by
  intro v; cases v <;> rfl

/-- boolOrLens is Idempotent. -/
theorem boolOrLens_idempotent : Idempotent boolOrLens := by
  intro v; cases v <;> rfl

end E213.Research.DiagonalClassification

namespace E213.Research.DiagonalClassification

open E213.Firmware E213.Hypervisor

/-! ## §3. Classification of Nat Lens — Escalate -/

/-- Lens.leaves is Escalate: sq v = v + v. -/
theorem leaves_escalate (v : Nat) :
    sq Lens.leaves v = v + v := rfl

/-- Lens.leaves is not Idempotent (counterexample: v = 1). -/
theorem leaves_not_idempotent : ¬ Idempotent Lens.leaves := by
  intro hI
  have h : (1 : Nat) + 1 = 1 := hI 1
  cases h

end E213.Research.DiagonalClassification

namespace E213.Research.DiagonalClassification

open E213.Firmware E213.Hypervisor E213.Research.F9Lens

/-! ## §4. Classification of F9 Lens — Multiply -/

/-- f9Lens is Multiply: sq v = F9.mul v v. -/
theorem f9Lens_multiply (v : F9) :
    sq f9Lens v = F9.mul v v := rfl

/-- f9Lens is not Idempotent (i² = -1 ≠ i). -/
theorem f9Lens_not_idempotent : ¬ Idempotent f9Lens := by
  intro hI
  have h : F9.mul F9.i F9.i = F9.i := hI F9.i
  have hne : F9.mul F9.i F9.i ≠ F9.i := by decide
  exact hne h

/-- f9Lens is not Collapse for any e (1² ≠ i²). -/
theorem f9Lens_not_collapse : ¬ ∃ e : F9, Collapse f9Lens e := by
  intro ⟨e, hC⟩
  have h1 : F9.mul F9.one F9.one = e := hC F9.one
  have h2 : F9.mul F9.i F9.i = e := hC F9.i
  have hne : F9.mul F9.one F9.one ≠ F9.mul F9.i F9.i := by decide
  exact hne (h1.trans h2.symm)

end E213.Research.DiagonalClassification
