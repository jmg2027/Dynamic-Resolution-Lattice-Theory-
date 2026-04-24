# 44 — 선택과 메타의 해소: 213 의 self-containment

## 이 노트의 위상

이 arc 에서 가장 큰 구조적 발견 중 하나.  Lens 기술을
쭉 전개하며 자연스럽게 드러난 meta 성질.

## §1. "선택" 이란 무엇인가 (in 213)

ZFC 의 AC: 집합들의 family 에서 대표를 뽑는 **abstract
함수의 존재** 보장.  구체는 특정 안 함.

Raw 에는 이런 abstract 의 자리가 없음:
- Raw 공리에 "고르기" primitive 동작 없음.
- pairing (slash) 은 **합치기** 이지 **고르기** 가 아님.
- "집합" 도 "family" 도 Raw-level 에 없음.

Raw 에서 선택이 발현되는 유일한 통로: **Lens specification**.

Lens L = 각 Raw 원소에 α-값 배정 = **각 입력에 대한 선택**.
Lens 를 하나 고르는 것이 선택의 전부.

## §2. AC 가 요구하던 "abstract 존재" 의 자리

ZFC: "선택 함수가 있다 (구체는 몰라도)".
213: 이런 진술이 **성립 불가능**.  "선택이 있다" 는 주장은
**구체 Lens 를 명시** 하거나 **아무 것도 아님**.

이는 Raw 가 Lens 를 **내재적 명세** 로 요구하기 때문:
- Lens 를 specify 안 하면 관측이 일어나지 않음.
- 관측 없으면 선택도 없음.
- 따라서 "abstract 존재" 는 Lens 가 있는 척만 하는 것 =
  자기모순.

## §3. Refines preorder 로 재진술

"L-class 에서 대표 뽑기" = "L 을 refine 하는 L' 찾기".

- L' ⊏ L 이고 L'.view 가 L-class 내부를 distinguish → 선택 수행.
- 최대 refinement = idLens (모든 class 를 singleton 으로 분해).
- 모든 선택은 idLens 까지의 사다리 어딘가.

AC 류 "존재 보장" 은 idLens 의 definition 에 이미 포함.
별도 공리 불필요.

## §4. Meta 의 일반적 해소

"선택" 의 경우는 더 큰 패턴의 일부.  **모든 "메타" 가 Lens
인스턴스로 내려옴**:

| 전통적 "메타" | 213 내부 대응 |
|---------------|---------------|
| AC (axiom of choice) | Lens specification |
| 외부 관측자 | Raw 원소 + Lens (AXIOM §8) |
| 무한 공리 | Lens 출력 phenomenon (Σ series) |
| Meta-213 | Lens 적용 (AXIOM §8.2) |
| Tarski truth | 특정 Lens 의 kernel |
| Universe hierarchy | Lens 중첩 (idLens 내부 반복) |
| Gödel meta-level | Raw.fold 의 self-reference |
| Consistency meta-proof | Lens 의 congruence 구조 |

## §5. 왜 이게 자동으로 작동하나

"메타" 하려면 **연산** 필요.  연산 = Lens.  Lens = 내부.
그러므로 메타 연산 = 내부 Lens.  메타 라고 부를 근거 소멸.

공리 수준 이유: AXIOM §8 이 "213 외부 없음" 을 명시.  외부
없음은 **조건** 이 아니라 **기본 상태** (CLAUDE.md 213 정체성).

## §6. 기존 internalization 과의 차이

- **HoTT / Univalent foundations**: 메타 구조를 type theory
  내부에 재구성.  메타 가 개념적으로는 여전히 존재.
- **Reflection principles**: V_κ 같은 large cardinal 을 내부
  에서 시뮬.  메타 가 작아졌지만 남아 있음.
- **213**: 메타를 **없앰** (재구성 아님).  애초에 만들지
  않았으므로 재구성할 것도 없음.

이것이 질적 차이 — 메타 를 "더 작게" 가 아니라 "완전 부재".

## §7. 진단적 가치 (물리 감사 도구)

Chapter 의 주장에서 "메타 신호" = fudge 신호:
- "외부 관측자" / "from outside" → Lens 로 환원?  안 되면 fudge.
- "meta level" / "higher type" → Lens 의 다른 출력?  안 되면 fudge.
- "axiom of X" 수입 → X 가 Raw + 명시적 Lens 에서 derive?
  안 되면 fudge.
- "consistency 는 명백" / "trivially holds" → 어떤 congruence?
  명시 못 하면 fudge.

모든 meta-vocabulary 가 **fudge 탐지 신호**.

## §8. 더 넓은 귀결

수학사의 역설 사이클:
1. 메타 계층 허용 → 내외 혼동 가능.
2. 혼동 → 역설 (Russell, Girard, Tarski).
3. 새 메타 층 도입 (Type theory, ZFC regularity).
4. 새 층 에서 혼동 재발.
5. 무한 regress.

213 은 (1) 을 거부 — 외부 층 없음이 공리 수준 서약.  사슬이
시작 안 됨.  모든 후속 역설 자동 소멸.

## §9. Arc 속도의 근저

이 arc 가 빠르게 진행된 이유의 일부: **메타 를 정리할 일이
없음**.  ZFC 기반 작업이라면:
- 각 증명마다 universe 계층 확인.
- AC / LEM 사용 추적.
- Small/large 구별.
- 구성적 vs 고전적 갈림.

213 에서는 이 부담 모두 없음.  오직 **Raw + Lens 의 derive
여부** 만 확인.  기계 검증이 남은 패치를 잡아냄.

## §10. 남은 점검

Q37.3 (quotient Lens 로 join) 의 재검토:
- AC 필요 없음 — Raw.toNat 의 canonical minimum 으로 대표
  선택 가능 (constructive).
- 구현은 heavy 하지만 공리적 cost 0.
- 다음 세션 후보.

## 변경 이력

- 2026-04-24: 선택 = Lens specification 관찰 + 메타 해소
  패턴.  AXIOM §8 의 구체 함의.  fudge 진단 도구.  Arc 속도
  의 근저 설명.
