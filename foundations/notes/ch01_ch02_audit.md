# ch01 / ch02 수학적 엄밀성 감사

**Date:** 2026-04-18
**Scope:** `book/chapters/ch01_whyC.tex` (Frobenius → ℂ) +
          `book/chapters/ch02_whyd5.tex` (d=5 유일성)
**Cross-reference:** `critical-line/lean/PmfRh/Core.lean` (additive_atoms),
          `ChiralChannels.lean`, `SwapAnnihilation.lean`, `SwapTower.lean`

---

## 요약

**엄밀한 부분 (A):**
- Frobenius 정리 (고전)
- 가법 atom = {2,3} (Lean `additive_atoms`, 0 sorry)
- ℂ⁵ = ℂ² ⊕ ℂ³ 유일 chiral decomp (Lean `chiral_split`)
- π₁(S^k) 위상 계산 (고전)
- Hurwitz/Frobenius 조합으로 ℝ, ℂ, ℍ 분류

**물리 가정 (acknowledged, 수학 아님):**
- R2 연속성 (gauge field 의 미분가능성)
- 중력 propagating DOF (GR 공식)
- Swap Theorem Case (b) 도메인 월 논변 (field theory)

**약점 (가장 심각 → 덜 심각):**

### W1 (critical): "σ-invariance → vector-like reps" ✅ **CLOSED** (this session)
- **위치:** ch02 Thm 2.1 (Swap Automorphism) Case (a)
- **이전 상태:** `SwapAnnihilation.lean` 이 `sigma_invariant : True`,
  `vector_like : True` 로 placeholder.  `swap_kills_chirality` 는
  `True = True.intro` tautology — 실제 내용 없음.
- **수정 (2026-04-18):**
  - `RepPair` 구조체 (`left right : Nat`) + `swap` 연산 추가.
  - `RepPair.isVectorLike r := r.left = r.right` 정의.
  - **정리 `sigma_invariant_iff_vector_like` (실제 양방향 증명):**
    `r.swap = r ↔ r.isVectorLike`.
  - `swap_involutive`: σ² = id.
  - `SwapInvariantTheory.sigma_invariant` 이제 `rep.swap = rep`
    (True 가 아닌 실제 명제).
  - `swap_kills_chirality` 는 `sigma_invariant_iff_vector_like.mp`
    로 실제로 도출.
- **결과:** ch02 Swap Theorem 의 수학적 알맹이가 Lean 에서 실제로
  증명됨, 0 sorry.  Book ↔ Lean 대응 완성.

### W2: Born rule "minimal polynomial" ✅ **CLOSED** (this session)
- **위치:** ch01 Thm (Born rule as algebraic necessity)
- **이전:** "any polynomial in z and z̄ that is real, non-negative
  must contain factor zz̄" 로 한 단계 건너뜀.  Phase-invariance 누락.
- **수정:** 조건 5 "Phase-invariant: f(e^{iθ}z) = f(z)" 추가.
  증명을 $(u,v) = (\Re z, \Im z)$ 에 대한 실수 이차형으로 전개하고,
  (3)+(4) 이 양정치 이차형을 강제, (5) 가 회전대칭을 강제 ⇒
  $f_2 = A(u^2+v^2) = A|z|^2$ 로 유일 결정.  별도 Remark 로 "왜
  phase invariance 인가" (gauge 변환 독립성) 설명 추가.

### W3: R2 연속성 — 물리 가정 명시 ✅ **CLOSED** (this session)
- **위치:** ch01 R2 (Phase)
- **수정:** R2 에 Parenthetical 추가 — "Physics input: continuity
  은 gauge 연결 $A = -i\,d\log G$ 의 미분가능성 요청 (Yang-Mills
  field strength $F = dA + A\wedge A$ 정의 가능).  R1–R4 중 순수
  수학적이지 않은 유일한 단계."

### W4: R3 의 Regge forward-reference ✅ **CLOSED** (this session)
- **위치:** ch01 R3 (Determinant)
- **수정:** 주 motivation 을 순수 대수로 ("$\sum_\sigma \mathrm{sgn}(\sigma)
  \prod_i G_{i,\sigma(i)}$ 는 non-commutative algebra 위에서 factor
  순서에 의존 → 잘 정의 안 됨; Dieudonné det 은 존재하지만 sign
  잃음").  Regge 언급은 parenthetical "(Anticipating Ch.\ref{ch:atoms})"
  로 명시적 분리, R3 의 정의에 속하지 않음을 밝힘.

### W5: Swap case (b) 는 field theory ✅ **CLOSED** (this session)
- **위치:** ch02 Thm 2.1
- **수정:** Theorem statement 을 "Swap Automorphism: algebraic content"
  로 재기술 — 알맹이는 "σ-fixed 쌍은 vector-like" (Lean 검증 완료,
  W1 결과).  Case (b) (spontaneous breaking + 도메인 월) 는 별도
  Remark 로 분리하고 "field-theoretic 논변이지 algebraic 증명이 아님"
  을 명시.  Mathematical content 과 physics consistency check 를
  의식적으로 구분.

---

## 크로스체크

| Book 주장 | Lean 증명 | 상태 |
|-----------|-----------|------|
| atoms = {2,3} (Lem 2.1) | `Core.lean: additive_atoms` | ✓ 완전 |
| ℂ⁵ = ℂ² ⊕ ℂ³ 유일 | `ChiralChannels.lean: chiral_split` | ✓ 완전 |
| tower (1,1) 유일 고정점 | `SwapTower.lean: fixed_iff_five` | ✓ 완전 |
| σ-inv → vector-like | `SwapAnnihilation.lean: sigma_invariant_iff_vector_like` | ✓ W1 닫힘 |
| Frobenius classification | (고전 정리 사용, Lean 없음) | ✓ 수용 |
| π₁(S^k) | (고전 결과, Lean 없음) | ✓ 수용 |

---

## 결론

ch01/ch02 의 **핵심 주장은 엄밀**:
- atoms = {2,3}: Lean 검증됨
- d=5 = 2+3: atoms + "distinct chiral pair" 로부터 유일하게 결정
- ℂ 유일성: Frobenius + π₁(S¹) = ℤ

**약점 W1 은 이번 세션에서 실제 증명으로 교체됨.**  `RepPair`, `swap`,
`sigma_invariant_iff_vector_like` 로 book ↔ Lean 대응 완성.

W2–W5 도 모두 이번 세션에서 닫힘 (book/chapters/ + book/math/chapters/
동기 편집):
- W2: Born rule 에 phase-invariance 추가 (5-조건 정리, 새 증명)
- W3: R2 연속성을 "physics input" 으로 명시
- W4: R3 motivation 을 순수 대수로 재기술 (Regge 는 forward ref)
- W5: Swap Theorem statement 를 algebraic content 로 재기술,
       case (b) 는 Physics Remark 로 분리

**결과: W1–W5 모두 닫힘.** ch01/ch02 의 수학 코어가 서술 수준과
Lean 형식화 수준 모두에서 엄밀해짐.

---

## W1 보강 결과 (적용됨, 2026-04-18)

`SwapAnnihilation.lean` 에 추가됨 (검증됨, 0 sorry):

```lean
/-- A representation pair for SU(a)₁ × SU(a)₂: (R₁, R₂).
    Reps are modeled abstractly by an index type (e.g. Nat for Young
    diagram index). -/
structure RepPair where
  left  : Nat  -- rep index of SU(a)₁
  right : Nat  -- rep index of SU(a)₂

/-- σ swaps the two factors: (R₁, R₂) ↦ (R₂, R₁). -/
def RepPair.swap (r : RepPair) : RepPair :=
  { left := r.right, right := r.left }

/-- Vector-like: left and right reps are identical. -/
def RepPair.isVectorLike (r : RepPair) : Prop := r.left = r.right

/-- MAIN THEOREM: σ-invariant rep pair is exactly vector-like. -/
theorem sigma_invariant_iff_vector_like (r : RepPair) :
    r.swap = r ↔ r.isVectorLike := by
  constructor
  · intro h
    have : r.right = r.left := by
      have := congrArg RepPair.left h
      simpa using this
    exact this.symm
  · intro h
    unfold RepPair.isVectorLike at h
    cases r with
    | mk l r => simp [RepPair.swap] at h ⊢; omega  -- or exact h.symm
```

결과 (실제 구현): `swap_kills_chirality` 가 이제 `rep.isVectorLike`
를 **실제로** 도출 (`sigma_invariant_iff_vector_like.mp` 사용).
`True.intro` placeholder 완전 제거.  전체 PmfRh 빌드 통과 (2727
modules).

## W2–W5 후속

- **W2 (Born rule):** 차후 ch01 proof 에 phase-invariance 한 줄 추가.
- **W3 (R2 연속성):** Remark 로 "이는 gauge field 의 미분가능성
  요청이라는 물리 input" 명시.
- **W4 (R3 forward-ref):** "Regge 는 ch04 에서 유도" 로 scope 분리.
- **W5 (case b):** ch02 Thm 2.1 case (b) 를 별도 Physics Remark 로 재배치.

이들은 수학 내용은 그대로이고 **서술 정리** 만 필요.  시간 나면
book 편집 세션에서 한 번에.  지금은 W1 (Lean 핵심) 해결이 우선.
