import E213.Lens.LensCore
import E213.Lens.Instances.Parity
import E213.Lens.Instances.Bool
import E213.Lens.Instances.F9

/-!
# Lens.Diagonal: Classification of the diagonal behavior of combine

Lean formalization of Note 34 §3 Q34.1.

Highlights the `combine v v` function (diagonal value) of each Lens
as `sq L : α → α`.  Four behaviors:

- **Collapse** (parityLens): `sq v = e` (constant).
- **Idempotent** (boolAndLens, boolOrLens): `sq v = v`.
- **Escalate** (Lens.leaves): `sq v = v + v`.
- **Multiply** (f9Lens): `sq v = v * v`.

Collapse + Idempotent simultaneously forces |α| = 1.
-/

namespace E213.Lens.Diagonal

open E213.Theory E213.Lens

/-- **Squaring function** — the α → α induced by the diagonal of a Lens. -/
def sq {α : Type} (L : Lens α) (v : α) : α := L.combine v v

/-- **Collapse** — diagonal collapses to a single point `e`. -/
def Collapse {α : Type} (L : Lens α) (e : α) : Prop :=
  ∀ v : α, L.combine v v = e

/-- **Idempotent** — diagonal is the identity. -/
def Idempotent {α : Type} (L : Lens α) : Prop :=
  ∀ v : α, L.combine v v = v

/-- Collapse and Idempotent simultaneously → every v equals e. -/
theorem collapse_idempotent_trivial {α : Type} (L : Lens α) (e : α)
    (hC : Collapse L e) (hI : Idempotent L) :
    ∀ v : α, v = e := by
  intro v
  have h1 : L.combine v v = e := hC v
  have h2 : L.combine v v = v := hI v
  exact h2.symm.trans h1

end E213.Lens.Diagonal

namespace E213.Lens.Diagonal

open E213.Theory E213.Lens
open E213.Lens.Instances.Parity E213.Lens.Instances.Bool

/-! ## §2. Classification of Bool Lenses -/

theorem parityLens_collapse : Collapse parityLens false := by
  intro v; cases v <;> rfl

theorem boolAndLens_idempotent : Idempotent boolAndLens := by
  intro v; cases v <;> rfl

theorem boolOrLens_idempotent : Idempotent boolOrLens := by
  intro v; cases v <;> rfl

end E213.Lens.Diagonal

namespace E213.Lens.Diagonal

open E213.Theory E213.Lens

/-! ## §3. Classification of Nat Lens — Escalate -/

theorem leaves_escalate (v : Nat) :
    sq Lens.leaves v = v + v := rfl

theorem leaves_not_idempotent : ¬ Idempotent Lens.leaves := by
  intro hI
  have h : (1 : Nat) + 1 = 1 := hI 1
  exact absurd h (by decide)

end E213.Lens.Diagonal

namespace E213.Lens.Diagonal

open E213.Theory E213.Lens
open E213.Lens.Instances.F9

/-! ## §4. Classification of F9 Lens — Multiply -/

theorem f9Lens_multiply (v : F9) :
    sq f9Lens v = F9.mul v v := rfl

theorem f9Lens_not_idempotent : ¬ Idempotent f9Lens := by
  intro hI
  have h : F9.mul F9.i F9.i = F9.i := hI F9.i
  have hne : F9.mul F9.i F9.i ≠ F9.i := by decide
  exact hne h

theorem f9Lens_not_collapse : ¬ ∃ e : F9, Collapse f9Lens e := by
  intro ⟨e, hC⟩
  have h1 : F9.mul F9.one F9.one = e := hC F9.one
  have h2 : F9.mul F9.i F9.i = e := hC F9.i
  have hne : F9.mul F9.one F9.one ≠ F9.mul F9.i F9.i := by decide
  exact hne (h1.trans h2.symm)

end E213.Lens.Diagonal
