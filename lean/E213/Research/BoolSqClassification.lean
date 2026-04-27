import E213.Research.DiagonalClassification
import E213.Research.NegSqLens

/-!
# Research.BoolSqClassification: Bool Lens 의 완전 diagonal 분류

note 35 + NegSqLens 의 완성: **Bool-valued Lens 의 sq 함수
는 정확히 4 가지** 중 하나.

모든 Lens Bool L 에 대해:
- Collapse L true (sq = const true), 또는
- Collapse L false (sq = const false), 또는
- Idempotent L (sq = id), 또는
- "NegSq" L (sq = !).

## 의의

Bool 의 자기-함수 공간이 유한하므로 (`Bool → Bool` 은 4
함수), diagonal 거동이 정확히 4가지.  일반 α 에서는 `α → α`
의 크기가 결정.
-/

namespace E213.Research.BoolSqClassification

open E213.Firmware E213.Hypervisor E213.Research.DiagonalClassification

/-- sq 가 negation 인 class. -/
def NegSq {α : Type} (L : Lens α) (f : α → α) : Prop :=
  (∀ v : α, L.combine v v = f v) ∧ (∀ v : α, f (f v) = v) ∧
  (∀ v : α, f v ≠ v)

/-- **Bool Lens 의 sq 완전 분류**. -/
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
