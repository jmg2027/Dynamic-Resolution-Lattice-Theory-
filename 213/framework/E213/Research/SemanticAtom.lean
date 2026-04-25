import E213.Hypervisor.Lens
import E213.Research.RawInitiality
import E213.Research.AxiomMinimality

/-!
# Research.SemanticAtom: 213 = 의미 의 atom (formal hub)

Note 75 의 thesis 의 형식 화 hub.  이전 의 vague framing
들 (constructive subset, fold-structured, scale-invariance)
모두 이 thesis 의 specific aspect 임 명시.

## Thesis (Mingu, 2026-04-25)

> 의미 를 갖는 어떤 것 도 213 을 벗어날 수 없다.  213 이
> semantic atom 이다.  213 의 axiom 보다 더 원초적 부재.
> 모든 것 이 213 atom 의 내부 이자 표현 이자 경계.

## Formal layer

| Layer | Lean 형식 |
|-------|---------|
| Distinguishing framework abstraction | `HasDistinguishing` typeclass |
| Raw 가 instance | `Raw.instHasDistinguishing` |
| Universal morphism | `Raw.fold` (이미 있음) |
| Initial object | RawInitiality.lean (기존) |
| Strict minimum | AxiomMinimality.lean (4 cases) |

## Thesis 의 Lean 형식 부분

이 파일 은 `HasDistinguishing` typeclass 로 의미 framework 의
abstraction 명시 — Raw 가 이 abstraction 의 strict minimum
(AxiomMinimality 의 4 case 가 negative direction).
-/

namespace E213.Research.SemanticAtom

open E213.Firmware E213.Hypervisor

/-! ### HasDistinguishing typeclass — 의미 framework 의 abstraction

"의미 를 갖는 framework" 의 minimum requirements:
1. 두 distinguishable base elements (a ≠ b).
2. Combining operation (binary).
3. Combine 의 symmetry (swap-invariance) — slash 의 commutativity.

(3) 가 없으면 encoding artifact 가 결과 에 leak — Raw axiom 의
slash_comm.  따라서 의미 framework 의 part. -/

class HasDistinguishing (α : Type) where
  a : α
  b : α
  distinct : a ≠ b
  combine : α → α → α
  combine_sym : ∀ x y, combine x y = combine y x

end E213.Research.SemanticAtom

namespace E213.Research.SemanticAtom

open E213.Firmware E213.Hypervisor

/-! ### Raw 가 HasDistinguishing instance

가장 자명 한 instance: Raw 의 a, b, slash 자체 가 axiom 만족.
slash_comm 이 combine_sym 의 직접 보존. -/

instance : HasDistinguishing Raw where
  a := Raw.a
  b := Raw.b
  distinct := by decide
  combine x y := if h : x = y then x else Raw.slash x y h
  combine_sym x y := by
    by_cases h : x = y
    · simp [h]
    · simp [h, Ne.symm h]
      apply Raw.slash_comm

end E213.Research.SemanticAtom

namespace E213.Research.SemanticAtom

open E213.Firmware E213.Hypervisor

/-! ### Universal morphism: Raw → α (HasDistinguishing α)

`HasDistinguishing α` 의 instance 에 대해, Raw 가 unique
morphism 으로 embed.  fold 가 universal morphism — Raw 가
"distinguishing framework" category 의 initial object.

(즉 213 의 axiom 이 *모든* 의미 framework 의 minimum.) -/

/-- Universal morphism Raw → α via fold. -/
def universalMorphism (α : Type) [d : HasDistinguishing α] : Raw → α :=
  Raw.fold d.a d.b d.combine

/-- Universal morphism preserves a. -/
theorem universalMorphism_a (α : Type) [d : HasDistinguishing α] :
    universalMorphism α Raw.a = d.a := rfl

/-- Universal morphism preserves b. -/
theorem universalMorphism_b (α : Type) [d : HasDistinguishing α] :
    universalMorphism α Raw.b = d.b := rfl

/-- Universal morphism preserves slash via fold_slash. -/
theorem universalMorphism_slash (α : Type) [d : HasDistinguishing α]
    (x y : Raw) (h : x ≠ y) :
    universalMorphism α (Raw.slash x y h)
      = d.combine (universalMorphism α x) (universalMorphism α y) := by
  unfold universalMorphism
  apply Raw.fold_slash _ _ _ d.combine_sym

end E213.Research.SemanticAtom

namespace E213.Research.SemanticAtom

open E213.Firmware E213.Hypervisor

/-! ### Lens 가 HasDistinguishing 의 specific instance

Lens α 의 view 는 HasDistinguishing α 의 morphism — 즉 Lens
는 의미 framework 의 instance 의 specific 형태.  Raw 가 모든
Lens 의 carrier (universal). -/

/-- Lens 가 HasDistinguishing 의 instance — base 의 distinctness
    + combine 의 swap-sym 을 hypothesis 로 받음.  일반 Lens 는
    constLens 같은 degenerate case 가 distinguishing 부재 (base_a
    = base_b) 가 가능 하므로, distinguishing 보존 Lens 만 instance.

    이 partial functoriality 가 "의미 의 atom 은 Raw, Lens 는
    그 위 의 representation" 의 형식 표현. -/
def lensToHasDistinguishing {α : Type} (L : Lens α)
    (h_distinct : L.base_a ≠ L.base_b)
    (h_sym : ∀ u v, L.combine u v = L.combine v u) :
    HasDistinguishing α where
  a := L.base_a
  b := L.base_b
  distinct := h_distinct
  combine := L.combine
  combine_sym := h_sym

end E213.Research.SemanticAtom
