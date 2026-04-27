import E213.Research.DiagonalClassification
import E213.Research.NegSqLens

/-!
# Research.BoolSqClassification: Complete diagonal classification of Bool Lenses

Completion of note 35 + NegSqLens: **the sq function of a Bool-valued
Lens is exactly one of 4 cases**.

For every Lens Bool L:
- Collapse L true (sq = const true), or
- Collapse L false (sq = const false), or
- Idempotent L (sq = id), or
- "NegSq" L (sq = !).

## Significance

Since the self-function space of Bool is finite (`Bool → Bool` has 4
functions), the diagonal behavior is exactly 4 cases.  For a general
α, the size of `α → α` determines the count.
-/

namespace E213.Research.BoolSqClassification

open E213.Firmware E213.Hypervisor E213.Research.DiagonalClassification

/-- sq 가 negation 인 class. -/
def NegSq {α : Type} (L : Lens α) (f : α → α) : Prop :=
  (∀ v : α, L.combine v v = f v) ∧ (∀ v : α, f (f v) = v) ∧
  (∀ v : α, f v ≠ v)

/-- **Complete classification of sq for Bool Lenses**. -/
theorem bool_sq_classification (L : Lens Bool) :
    Collapse L true ∨ Collapse L false ∨ Idempotent L
    ∨ (∀ v : Bool, L.combine v v = !v) := by
  have hT := L.combine true true
  have hF := L.combine false false
  -- 4 cases by hT, hF ∈ Bool
  rcases h1 : L.combine true true with _ | _ <;>
  rcases h2 : L.combine false false with _ | _
  · -- sq T = false, sq F = false: Collapse false
    right; left
    intro v; cases v; exact h2; exact h1
  · -- sq T = false, sq F = true: sq = negation
    right; right; right
    intro v; cases v; exact h2; exact h1
  · -- sq T = true, sq F = false: sq = id → Idempotent
    right; right; left
    intro v; cases v; exact h2; exact h1
  · -- sq T = true, sq F = true: Collapse true
    left
    intro v; cases v; exact h2; exact h1

end E213.Research.BoolSqClassification
