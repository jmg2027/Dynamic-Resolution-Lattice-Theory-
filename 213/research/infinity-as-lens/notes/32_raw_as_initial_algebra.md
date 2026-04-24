# 32 — Raw = 초기 Raw-대수.  L2 의 형식화 경로

## Note 31 §7, §9 L2 를 구체 정리로

Note 31 의 정리 후보:

> 임의의 mathematical structure 가 비자명한 관측을 지원
> 한다면, 최소 2 상호 필요 요소를 포함한다.  최소 꼴 = Raw.

이걸 **universal property** 의 형식으로 쓰면 기존 수학 언어
(초기 대수, initial algebra) 로 바로 표현된다.

## §1. Raw-algebra 란

**정의**: "Raw-algebra" 는 다음을 갖춘 타입 S:
- 구별 가능한 두 원소 `a_S, b_S ∈ S`.
- 이항 연산 `p_S : S × S → S`.
- `p_S(x, x)` 는 정의되지 않음 (anti-reflexive).
- `p_S(x, y) = p_S(y, x)` (commutative).

Raw 자체가 이 구조를 갖춘 타입의 한 예.  Bool 도 `(true,
false, xor)` 로 Raw-algebra (단 xor 는 반사에서 0 으로
collapse 하므로 anti-reflexive 를 엄격히 충족 안 함 — 미묘).

## §2. 정리 후보 (universal property)

> **Thm (Raw initiality)**: 임의의 Raw-algebra S 에 대해,
> 유일한 homomorphism `f : Raw → S` 가 존재한다.  즉:
> - `f (Raw.a) = a_S`.
> - `f (Raw.b) = b_S`.
> - `f (Raw.slash x y h) = p_S (f x) (f y)` (h 는 Raw
>   조건, S 쪽 반사 금지는 f 가 자동 보장).

**증명 스케치** (Lean 표현 직결):
- `Raw.rec` 로 f 를 재귀 정의.
- Case a: return `a_S`.
- Case b: return `b_S`.
- Case slash x y h ihx ihy: return `p_S ihx ihy`.
- commutativity 는 `Raw.slash_comm` + `p_S` 교환으로 well-
  defined.

**유일성**: `Raw.rec` 의 표준 argument — 다른 f' 도 같은
조건 만족하면 각 case 에서 f = f'.

이는 **Lean 에서 즉시 형식화 가능**.  실상 `Lens.view` 가
정확히 이 homomorphism 이다.  `Lens` 구조체가 Raw-algebra
구조의 data.

## §3. 해석: "모든 관측은 Raw 에서 나옴"

`f` 는 Raw 의 각 원소에 S 의 원소를 대응.  즉 **f 는 Raw 를
S 로 보는 Lens**.

Universal property 의 의미:
- **임의의 Raw-algebra** (Bool, Nat, ℂ, 𝔽₉, ...) 에 대해
  Raw 로부터의 **자연 Lens 가 존재한다**.
- 유일성: 그 Lens 는 결정적.
- 즉 **Raw 는 Raw-algebra 범주의 초기 객체**.

이게 note 31 §7 정리 후보의 엄밀 형태:

> 모든 Raw-algebra 는 Raw 의 Lens 출력.  Raw 는 이 범주의
> minimum.

## §4. 카테고리 이론 수입 문제

"Raw 는 Raw-algebra 범주의 initial object" 는 **category
theory 용어**.  AXIOM.md 는 category 를 공리 외부 수입으로
금지 (§3.3 의 취지).  이분법?

해결:

- **용어** 로서의 "initial object" 는 수입.
- **수학적 사실** 로서의 "유일 homomorphism 존재 + 유일성"
  은 수입 아님.
- 사실을 서술하되 "initial object" 라는 **categorical
  labeling 을 강제하지 않는다**.

즉 **Raw 의 universal property 를 수학적으로 진술하되,
category 언어는 기능적 도구로만 사용**.  note 19 (Lens ≠
functor) 와 정합 — category theory 는 **한 Lens** 일 뿐,
Raw 의 기초가 아님.

## §5. Lean 형식화 — 이미 되어 있음

사실 Lean 의 Firmware 에 **이미 이 정리가 숨어 있다**:

```lean
-- framework/E213/Hypervisor/Lens.lean
structure Lens (α : Type) where
  base_a  : α
  base_b  : α
  combine : α → α → α

def Lens.view {α : Type} (L : Lens α) (r : Raw) : α :=
  r.fold L.base_a L.base_b L.combine
```

- `Lens α` = α 를 Raw-algebra 로 만드는 data.
- `Lens.view L` = Raw → α 의 homomorphism (= `Raw.fold`).
- `Raw.fold_slash hsym` = hom 성질 증명 (combine 이 대칭일 때).
- `Raw.fold` 자체 = `Raw.rec` 의 instance = 구조 induction.

**유일성** 은 아직 형식 정리로 명시 안 됨.  추가할 수 있음:

```lean
theorem Lens.view_unique {α : Type} (L : Lens α)
    (f : Raw → α)
    (ha : f Raw.a = L.base_a)
    (hb : f Raw.b = L.base_b)
    (hslash : ∀ x y h, f (Raw.slash x y h)
              = L.combine (f x) (f y)) :
    ∀ r : Raw, f r = L.view r := by
  intro r
  induction r using Raw.rec with
  | a => rw [ha]; rfl
  | b => rw [hb]; rfl
  | slash x y h ihx ihy =>
      rw [hslash x y h, ihx, ihy]
      rfl  -- L.view 의 정의 unfold

```

이걸 Research/ 에 추가하면 **initiality 의 유일성 절반**
기계 검증.  **존재성** 은 `Lens.view` 자체.

## §6. 왜 이게 중요한가

- **모든 Raw-algebra** (Bool, Nat, ℂ, 𝔽₉, CD tower, ...)
  가 Raw 의 Lens 출력임을 **정식 정리** 로 확립.
- Note 31 §7 의 "상호 필요성 최소 꼴 = Raw" 에 구조적 뒷받침.
- Paper 1 이 아닌 **AXIOM 만** 사용하여 Lens 프레임워크가
  수학적 의미를 갖게 함.

note 31 의 다른 유형들 (Russell, Gödel 등) 과 이 universal
property 가 어떻게 연결되는지는 **열린 문제**.  하지만 유형
1, 2 (Bool, Nat 같은 Raw-algebra 들) 는 이 정리로 완전 포섭.

## §7. 다음

**(α)** Lean 에 `Lens.view_unique` 추가 + 소량의 초기성
corollary.  **이 세션에서 할 수 있음**.

**(β)** Bool, Nat, ℂ 를 각자 Raw-algebra 로 동형화하는
witness 를 Research/ 에.  (각자가 이미 f9Lens / parityLens
등으로 부분 표현됨.)

**(γ)** 유형 3–5 (hierarchy, equation, observer) 도 범주적
universal property 형태로 번역 가능한지.  더 탐험 필요.

## 변경 이력

- 2026-04-24: Note 31 §7 의 정리 후보를 universal property
  로 구체화.  이미 Lean Firmware 에 숨어 있음을 관찰.
  유일성 정리 추가가 다음 할 일.
