# 82 — DistMorphism: distinguishing-framework category 의 형식

`Research/DistMorphism.lean` — `HasDistinguishing` instance 들
사이 의 structure-preserving morphism α → β 의 정식 형식.

## 결과

```lean
structure DistMorphism (α β : Type) [d_α : HasDistinguishing α]
    [d_β : HasDistinguishing β] where
  toFun : α → β
  preserves_a : toFun d_α.a = d_β.a
  preserves_b : toFun d_α.b = d_β.b
  preserves_combine : ∀ x y, toFun (d_α.combine x y)
                              = d_β.combine (toFun x) (toFun y)

def id (α) [HasDistinguishing α] : DistMorphism α α
def comp : DistMorphism α β → DistMorphism β γ → DistMorphism α γ

theorem comp_assoc : comp (comp f g) h = comp f (comp g h)
theorem id_comp : comp (id α) f = f
theorem comp_id : comp f (id β) = f
```

모든 결과 가 **axiom 부재** (pure constructive, rfl).

## 의의

distinguishing-framework category 의 정식 형식:
- Objects: `HasDistinguishing α` instance.
- Morphisms: `DistMorphism α β`.
- Identity, composition, associativity, neutrality — 모두 ✓.

이게 framework 의 categorical structure 의 axiom-free 명시 —
*완전 constructive* category.

## Raw 의 categorical position (design note)

`universalMorphism α : Raw → α` 가 `DistMorphism Raw α` 의
candidate.  하지만 *모든* combine case 보존 부재 — Raw 의 자명
instance 가 idempotent (`combine x x = x`) 인 데, 일반 instance
는 idempotent 부재 (e.g., Nat with + 는 `1 + 1 = 2`).

이건 design problem 이 아니라 **feature**:
- Raw 의 fold structure 가 distinct args 만 다룸 (axiom 4 의
  reflection — `slash x y h` 가 `x ≠ y` 가정).
- 일반 morphism α → β 는 ideally 모든 (x, y) preserve.
- Raw 의 specific position: distinct args 만 의 morphism (Lens.view
  의 form).

따라서 Raw → α 의 morphism 은 두 form:
1. `Lens α` (Hypervisor): distinct case 만, fold-structured.
2. `DistMorphism Raw α` (이 file): 모든 case, 일반 sense — Raw 의
   combine 의 idempotent 가 align 부재.

Raw 의 *RawInitiality* 형식 (raw_initial in SemanticAtom) 이
form 1 의 universal property — `Lens.view` 가 unique fold-structured
morphism.

## Note 75-81 와 의 관계

| Note | Direction |
|------|-----------|
| 75 | Conceptual thesis. |
| 76 | Self-application (Prop instance). |
| 77 | Function-level boundary. |
| 78 | Lens-level closure (canonical form). |
| 79 | Universal property (Raw initial). |
| 80 | Carrier vs reach. |
| 81 | Reach dichotomy + image closure. |
| **82** (이) | **Categorical structure** (DistMorphism category). |

8 angle 모두 의미 atom thesis 의 evidence.  framework 가
*categorical 으로 잘 정의 된* 의미 framework.

## Axiom 검증

`#print axioms`:
- `id`, `comp`: no axioms.
- `comp_assoc`, `id_comp`, `comp_id`: no axioms.

모두 reflexivity — 가장 sober minimum.

## 변경 이력

- 2026-04-25: DistMorphism.lean 작성.  Identity + composition +
  category laws.  의미 atom thesis 의 categorical 기반.
