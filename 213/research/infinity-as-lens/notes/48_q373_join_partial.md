# 48 — Q37.3 Quotient Lens / Join 의 partial 해결

## 진전

### 해결된 부분 (Lean)

`Research/JoinEquiv.lean`:

- **`JoinEquiv L M`**: inductive relation with constructors
  `ofL`, `ofM`, `refl`, `symm`, `trans`, `slash_cong`.
- `L.equiv ⊆ JoinEquiv L M` (via `ofL`).
- `M.equiv ⊆ JoinEquiv L M` (via `ofM`).
- JoinEquiv 는 **slash-congruence** (slash_cong constructor).
- JoinEquiv 는 **equivalence** (refl/symm/trans).
- **`JoinEquiv_is_least`**: 임의 Lens N 에 대해
  `L.refines N ∧ M.refines N → N.equiv ⊇ JoinEquiv L M`.

즉 **JoinEquiv L M 이 L.equiv ∪ M.equiv 를 포함하는 가장 작은
slash-congruence 동치 관계**.  Refines preorder 의 **Join**.

### 미해결 부분 (Lean)

**JoinEquiv 를 정확히 kernel 로 가지는 concrete Lens 구성**:

Quot-based 시도:
```
abbrev JoinQuot := Quot (JoinEquiv L M)
def combineRaw (u v : Raw) : JoinQuot :=
  if h : u ≠ v then Quot.mk _ (Raw.slash u v h) else ???
```

`combineRaw` 의 well-definedness 가 깨짐: JoinEquiv u u' ∧
JoinEquiv v v' 에서 `u ≠ v` 이지만 `u' = v'` 인 경우, 두 식이
같은 Quot 값을 내야 하는데 보장 안 됨.

## 문제의 본질

Class [C] 가 multiple Raw-representatives 를 가질 때, diagonal
(u = v) 과 off-diagonal (u ≠ v) 이 혼재.  Combine 이 두 경우
에서 다른 값을 내면 well-definedness 깨짐.

해결 방법:
1. **Canonical rep 선택**: 각 class 에서 Raw.toNat 최소값 선택.
   그러면 class 안에서 일관된 "diagonal/off-diagonal" 판정
   가능.  하지만 Raw.toNat 이 Internal 의존 — 추상 위반.
2. **JoinEquiv 의 추가 relation**: "slash(u, v) ~ 적절한 fallback"
   을 constructor 로 강제.  어떤 fallback 이 자연스러운지 불명.
3. **Different 기본 Lens**: 다른 codomain 선택.

## 실질적 충분성

**정리 형식 결과는 이미 충분**:

- JoinEquiv 가 존재 (Lean 에서 inductive로 정의).
- Universal property 로 "Join kernel" 로 확립.
- Any Lens that refines both 은 이 relation 을 포함.

**Concrete Lens 가 필요한 경우**만 (physics chapter 감사, 
수치 계산) Quot-based 구성 필요.  대부분의 구조 분석은
universal property 만으로 충분.

## Note 44 (선택 = Lens specification) 과의 일관성

Q37.3 의 "concrete Lens construction" 이 막히는 지점이 정확히
**어떤 specific Lens 를 택할지 명시해야** 결정되는 지점.  이는
note 44 의 "선택 = Lens specification" 원칙과 정합.

추상적 존재 (JoinEquiv universal property) 는 확보; 구체 선택
(어떤 Lens 인스턴스) 은 context-dependent.

## 실용적 귀결

Q37.3 의 **이론적 측면**은 완성:
- Join 은 존재 (JoinEquiv 로 represented).
- Join 은 unique (universal property 로 characterize).
- Refines preorder 가 join-semilattice **kernel level** 에서.

Q37.3 의 **concrete Lens 측면**은 open — 별도 세션에서 
Raw.toNat 같은 auxiliary tool 로 시도 가능.

## 결론

Q37.3 **partial resolution**:
- ✓ Join relation 정의 (JoinEquiv).
- ✓ Universal property (least).
- ✗ Concrete Lens 구성.

Partial 이어도 구조적 의의는 완결 — Lens kernel 공간이
**complete lattice** 임을 보장 (meet + join + bounds).

## 다음

- Concrete Lens 구성은 future work.
- Physics chapter 감사 (별도 arc) 로 전환.
- Bezout chain 으로 일반 Join = gcd 도 future work.

## 변경 이력

- 2026-04-24: Q37.3 partial resolution.  JoinEquiv inductive
  + universal property Lean 증명.  concrete Lens 구성은 open.
