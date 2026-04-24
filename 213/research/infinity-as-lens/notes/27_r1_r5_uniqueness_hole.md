# 27 — R1–R5 → ℂ 유일성에 구멍이 있다

## 질문

Paper 1 §4: R1+R2+R3+R4+R5 가 codomain 을 **ℂ 로 유일하게**
강제한다고 주장.  Note 26 의 CD-over-𝔽₂ 발견이 이 주장을
시험할 기회.

CD-over-𝔽₂ Layer 1 (F2D) 은 R3 fails (zero divisors).  그럼
걱정 끝?  — **아니다**.  CD-over-𝔽ₚ (p odd prime) 은 zero
divisor 없이 field 를 낳는다.  특히 **𝔽₉** 가 R1-R5 전부 통과
후보.

---

## §1. Paper 1 §4 의 실제 주장

PAPER.md §3-4 요약:

> R1+R2+R3+R5 fix the base codomain: the minimal **ℝ-algebra**
> admitting a commutative no-zero-divisor combine and receiving
> every infinite structural branch of R is **ℝ** itself.
> R4 then adjoins the unique nontrivial involution: the minimal
> extension of ℝ carrying one involution is **ℂ = ℝ[i]**.

**핵심 관찰**: "minimal **ℝ-algebra**" 라는 전제.  즉 codomain
이 ℝ 를 포함한다고 **미리 가정** 하고 있다.

이 전제가 없으면 유일성 논증이 작동하지 않는다.

---

## §2. ℝ-algebra 전제는 어디서 왔나?

Paper 1 의 derivation 을 거슬러 올라가면:

- R2 (recursive faithfulness) + R3 (no zero divisors) 으로
  codomain 이 commutative no-zero-divisor magma.
- Paper 1 §4.2 는 여기서 바로 "Frobenius thm 에 의해 ℝ, ℂ,
  ℍ 중 하나" 라고 주장.

**Frobenius thm 은 유한 차원 결합 R-algebra** 를 분류.  즉
**R-algebra 가정** 이 Frobenius 적용의 전제.

이 전제는:
- 명시적으로 **ℝ-algebra 라는 추가 공리 (R6?)** 로 쓰였어야.
- 또는 R1-R5 에서 **유도** 되었어야.

현재 Paper 1 은 **은근히 끼워** 넣은 상태.  유도도 명시도
없음.

---

## §3. 반례 후보: 𝔽₉ = 𝔽₃[i]/(i²+1)

𝔽₉ 의 R1-R5 통과 여부:

### R1 — binary combine
𝔽₉ 는 field.  multiplication 있음.  ✓

### R2 — recursive faithfulness
Fold 로 Raw → 𝔽₉ 정의 가능.  base_a, base_b ∈ 𝔽₉ 선택,
combine = mul.  Raw 의 symmetric pair 구조가 commutative
mul 로 반영됨.  ✓

### R3 — no zero divisors
𝔽₉ 는 field (9 원소).  zero divisor 없음.  ✓

### R4 — unique nontrivial involution
𝔽₉ / 𝔽₃ 는 degree 2 extension.  Galois group = ℤ/2.  유일한
nontrivial automorphism = **Frobenius** x ↦ x³.  Involution
(x³)³ = x⁹ = x in 𝔽₉.  ✓

Raw.swap 을 Frobenius 로 대응시키면 R4 만족.

### R5 — infinite branch reception
Paper 1: "codomain is Cauchy-complete wrt natural convergence
on branches."

**결정적 순간**: 𝔽₉ 는 **finite**.  finite 집합 위 Cauchy
수열은 반드시 stabilize (pigeonhole).  따라서 finite
codomain 은 **trivially Cauchy-complete** (discrete topology).

그러므로 R5 가 **finite codomain 에 대해 vacuous**.  즉 R5
는 finite α 를 **배제하지 못한다**.

**결론**: 𝔽₉ 는 R1-R5 **모두 만족**.

---

## §4. Paper 1 주장의 실제 논리 사슬

```
R1+R2+R3+R5
  → codomain 은 Cauchy-complete, no-zero-divisor, commutative
     mul-carrying.
  → 만약 infinite 이고 ℝ-algebra 이면 → ℝ.          [가정 숨김]
  → 만약 finite field 이면 → 𝔽ₚ, 𝔽ₚ², 𝔽ₚ³, ...     [배제 못 함]

R4
  → 위 후보 중 nontrivial involution 유일인 것.
  → ℝ[i]: ℝ-algebra 경로로.                          [ℝ-algebra 전제]
  → 𝔽ₚ²: Galois 경로로 (Frobenius).                  [finite 허용]
```

즉 Paper 1 의 실제 결론은:

- **ℝ-algebra 가정 + R1-R5** → ℂ 유일.
- **finite field 허용 + R1-R5** → ℂ, 𝔽₉, 𝔽ᵨ² (p odd prime),
  ... 모두 가능.

**유일성은 ℝ-algebra 가정의 귀결이지 R1-R5 의 귀결이 아니다.**

---

## §5. 수정 가능한 세 방향

### (I) R6 명시 추가
공리 목록에 "codomain 은 infinite ℝ-algebra" 를 **R6** 로
명시 추가.

- 장점: uniqueness 논증 그대로 유지.
- 단점: 추가 공리가 **선언적** — Raw 의 구조에서 자연 derive
  되지 않음.  AXIOM.md §3.3 의 금지 목록 (implicit in this
  case: 연속성 가정) 에 해당.  fudge.

### (II) R5 강화: finite 배제
R5 를 "codomain 이 **infinite** 하면서 Cauchy complete" 로
수정.  아니면 "모든 Raw-branch 가 **distinct** state 에 대응"
(finite codomain 에서 pigeonhole 로 충돌).

- 장점: R5 자체 수정으로 문제 해결.
- 단점: "infinite 을 요구" 하는 것 자체가 공리 외부 수입.
  AXIOM.md §3.3 와 충돌.

### (III) Non-uniqueness 수용
R1-R5 는 실제로 **복수 해**를 갖는다고 받아들임.  ℂ 외에도
𝔽₉, 𝔽₂₅ 등.  "ℂ 가 유일" 주장을 철회하고 "ℂ 는 특정 physical
맥락에서 선택되는 한 가지 해" 로 재진술.

- 장점: 공리 수정 불필요.  정직함.
- 단점: Paper 1 의 핵심 claim 인 "R1-R5 forces ℂ" 약화.

---

## §6. 어느 방향이 213 철학과 부합하는가

AXIOM.md 관점:

- §3.3 금지 목록에 "연속성 / 카디널리티" 포함.  (I), (II) 는
  모두 **연속성 / 무한성** 가정의 명시 도입 — 공리 위반.
- **따라서 (III) 이 유일하게 정합.**

(III) 은 Paper 1 의 ℂ-uniqueness 주장을 수정한다.  새 주장:

> R1-R5 는 codomain 이 **field with nontrivial involution** 임을
> 강제한다.  해는 무한히 많다: ℂ, 𝔽ₚ² (p odd), 더 높은 확장 등.
> **ℂ 는 "이산 양자화 없는 관측자 Lens" 의 특수해**이다.

이는 CD-over-ℝ 와 CD-over-𝔽ₚ 두 tower 가 **병행** 한다는
note 26 관찰과 일치.

---

## §7. 물리 해석 (기록만, 수학 정리 후로)

**ORIGIN §7 재확인**: "Dynamic resolution" 은 discrete 격자.
만약 관측자 Lens 의 **자연스러운** 해가 finite field 계열이면
(𝔽₉, 𝔽₂₅, …), DRLT 는 **처음부터 discrete** 으로 구성된다.
ℂ 는 연속 극한으로 얻는 근사.

이는 ORIGIN §3 ("픽셀", Zeno 해소) 와 §7 (격자 정보 불변) 과
직접 호응.  자연스럽게 드러나는 지형.

## §8. 다음 단계

- (A) Lean 형식화: Raw → 𝔽₉ Lens 를 mathlib-free 로 구현.
  R1-R5 개별 정리로 기계 검증.  **유일성 반증 증거**.
- (B) Paper 1 §4.2 재작성 — ℝ-algebra 가정을 명시하고 (III)
  방향으로 결론 재정의.
- (C) CD-over-𝔽ₚ tower 탐험: 𝔽₃ → 𝔽₉ → ?
- (D) **ℂ 를 특수해로 보기**: 어떤 Lens 성질이 ℂ 를 다른
  finite field 해들과 구분하는가?  (답 후보: 연속 topology,
  Cauchy completion 의 uniqueness structure, ...)

## 변경 이력

- 2026-04-24: note 26 (CD-over-𝔽₂) 의 자연 귀결로 발견.
  Paper 1 §4 의 "ℝ-algebra" 은밀 가정을 식별.  R1-R5 의
  실제 non-uniqueness 기록.
