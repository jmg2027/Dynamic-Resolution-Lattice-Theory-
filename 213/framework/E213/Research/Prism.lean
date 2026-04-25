import E213.Hypervisor.Lens

/-!
# Research.Prism: Lens 의 categorical dual

User directive (2026-04-25): "Lens 의 쌍대 (Prism) 개념 을 213 의
문법 으로 가져와 대수적 dual 을 구축".

Functional programming 의 Prism 의 213-form:
- `preview : Raw → Option α` (partial getter).
- `review : α → Raw` (constructor / injection).
- coherence: review 후 preview 가 round-trip.

## 의의

Lens 가 Raw 의 *모든* element 를 α 로 view (total).
Prism 이 Raw 의 *specific case* 만 α 로 extract (partial) +
α 의 element 를 Raw 로 inject (constructor).

→ Lens = product accessor, Prism = sum/coproduct accessor.

## Concrete instances

- `aPrism : Prism Unit` — Raw.a 의 case.
- `bPrism : Prism Unit` — Raw.b 의 case.

각 prism 이 Raw 의 specific element 를 *distinguishably* extract.
-/

namespace E213.Research.Prism

open E213.Firmware E213.Hypervisor

/-- 213-style Prism: Lens 의 categorical dual.

    `preview` 가 specific case 의 partial extraction.
    `review` 가 그 case 의 element 의 constructor.
    coherence 가 round-trip property. -/
structure Prism (α : Type) where
  preview : Raw → Option α
  review : α → Raw
  coherence : ∀ a, preview (review a) = some a

end E213.Research.Prism

namespace E213.Research.Prism

open E213.Firmware E213.Hypervisor

/-- Decidable equality on Raw 으로 부터 specific case Prism. -/
def caseElement (target : Raw) : Prism Unit where
  preview r := if r = target then some () else none
  review _ := target
  coherence := fun _ => by
    show (if target = target then some () else none) = some ()
    rw [if_pos rfl]

/-- Raw.a 의 case Prism. -/
def aPrism : Prism Unit := caseElement Raw.a

/-- Raw.b 의 case Prism. -/
def bPrism : Prism Unit := caseElement Raw.b

end E213.Research.Prism

namespace E213.Research.Prism

open E213.Firmware E213.Hypervisor

/-- aPrism preview 가 Raw.a 에서 some, Raw.b 에서 none. -/
theorem aPrism_a : aPrism.preview Raw.a = some () := by
  unfold aPrism caseElement
  show (if (Raw.a : Raw) = Raw.a then some () else none) = some ()
  rw [if_pos rfl]

theorem aPrism_b : aPrism.preview Raw.b = none := by
  unfold aPrism caseElement
  show (if (Raw.b : Raw) = Raw.a then some () else none) = none
  rw [if_neg (by decide)]

theorem bPrism_a : bPrism.preview Raw.a = none := by
  unfold bPrism caseElement
  show (if (Raw.a : Raw) = Raw.b then some () else none) = none
  rw [if_neg (by decide)]

theorem bPrism_b : bPrism.preview Raw.b = some () := by
  unfold bPrism caseElement
  show (if (Raw.b : Raw) = Raw.b then some () else none) = some ()
  rw [if_pos rfl]

end E213.Research.Prism
