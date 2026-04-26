# E1 — Real213 위 *전 체* 해 석 학 / 미적분 의 marathon roadmap

## 목표

Real213 을 native ℝ 으 로 받 아 들 이 고, **Bishop-style
constructive analysis 의 full program** 을 framework-internal 형식
화.  ZFC ℝ 와 의 mapping 시도 부재 — *213 만 의* analysis.

## 방법론

- Lean 4 core only (no Mathlib).
- 0 sorry, 0 external axioms (≤ propext + Quot.sound).
- Bishop (1967) + Bridges-Vita (2006) literature 의 213-internal
  rebuild — *그 program 은 prior art*, 213 의 contribution 은
  *substrate uniformity* (Lens) + *machine verification*.
- 막 히는 곳 = framework 의 진 짜 boundary candidate (CLAUDE.md
  falsifiability 적용).

## Phase A — Real213 의 type-level foundation

| # | Milestone | Status | 파일 |
|---|-----------|--------|------|
| A1 | Real213 type 정의 | ✓ done | `Real213.lean` |
| A2 | equivalence (refl/symm/trans) + Setoid | ✓ done | `Real213Equiv.lean` |
| A3 | Constant embedding (Raw → Real213) | ✓ done | `Real213Const.lean` |
| A4 | Order (le, lt) — Bishop-style | ✓ done | `Real213Order.lean` |
| A5 | Constructive sign / positivity | ✓ done | `Real213Sign.lean` |

**A4 의 challenge**: order proxy = orderProj m k 의 정확 한 사용.
le 의 전형 적 정의: ∀ k ≥ 1, ∃ N, ∀ i ≥ N, projection inequality
holds with margin 1/k.

**A5 의 challenge**: trichotomy 의 *constructive* form — `r > 0
∨ r ≤ ε` 의 weak form (full LEM trichotomy 부재).

## Phase B — Arithmetic structure

| # | Milestone | Status | Notes |
|---|-----------|--------|-------|
| B1 | Addition | pending | sequence-wise + modulus.N max combine |
| B2 | Negation | pending | Raw 의 a/b swap 활용? abLens-internal swap |
| B3 | Multiplication | pending | bounded sequence 의 product modulus |
| B4 | Division (with positivity) | pending | r ≠ 0 의 *modulus* 형식 |
| B5 | equiv 의 algebraic 호환 | pending | `r ~ r' → r + s ~ r' + s` 등 |

**B 의 핵심**: addition 의 modulus 가 *sum* 의 modulus 가 *각각의
modulus 의 max* (or +1 보 정).  Bishop §1.2 의 standard result.

## Phase C — Convergence + Cauchy completeness

| # | Milestone | Status |
|---|-----------|--------|
| C1 | Real213-valued sequence | pending |
| C2 | Real213 sequence 의 Cauchy 정의 | pending |
| C3 | Real213 의 Cauchy completeness (Cauchy → limit) | pending |
| C4 | Convergence of monotone bounded sequence (constructive form) | pending |

**C3 의 기초**: Real213 자체 가 (sequence + modulus) pair 이 므 로
Cauchy completeness 가 *almost trivial* — Bishop 의 핵심 우 회.

## Phase D — Continuity

| # | Milestone | Status |
|---|-----------|--------|
| D1 | Real213 → Real213 function type | pending |
| D2 | Continuity (modulus form, Bishop-style) | pending |
| D3 | Uniform continuity on bounded interval | pending |
| D4 | Composition + arithmetic 보존 | pending |
| D5 | Constant + identity 함수 가 continuous | pending |

## Phase E — Differentiation

| # | Milestone | Status |
|---|-----------|--------|
| E1 | Difference quotient | pending |
| E2 | Differentiability (modulus form) | pending |
| E3 | Sum/product rule | pending |
| E4 | Chain rule | pending |
| E5 | Mean value theorem (constructive form) | pending |

## Phase F — Integration

| # | Milestone | Status |
|---|-----------|--------|
| F1 | Riemann partition | pending |
| F2 | Riemann sum 의 Cauchy sequence | pending |
| F3 | Integral 의 정의 (continuous integrand 만) | pending |
| F4 | 미적분 의 기 본 정리 (FTC) | pending |
| F5 | Linearity, monotonicity | pending |

## Phase G — Specific functions

| # | Milestone | Status |
|---|-----------|--------|
| G1 | exp, log via power series | pending |
| G2 | sin, cos via power series | pending |
| G3 | π 의 framework-internal definition | pending |
| G4 | e 의 ditto (이미 EulerCombinatorialPure 부분 보 유) | partial |

## Phase H — Specific theorems

| # | Milestone | Status |
|---|-----------|--------|
| H1 | IVT (constructive, with explicit interval halving modulus) | pending |
| H2 | Extreme value theorem (uniform continuous on compact) | pending |
| H3 | Taylor expansion | pending |
| H4 | 익명 ε-N 의 explicit modulus 형 표현 | pending |

## 진 행 우선 순위 (suggested)

1. **A4 + A5** (order + sign) — analysis 의 most basic.  ~수 일.
2. **B1 + B5** (addition + equiv 호환) — arithmetic 첫 단계.
3. **C3** (Cauchy completeness) — *almost trivial* given Real213
   의 정의.  big symbolic milestone.
4. **D1-D5** (continuity) — 기본 calculus 의 substrate.
5. ... 이후 marathonically.

## Estimated effort

각 milestone ≈ 1-3 Lean 파일 (각 ≤ 80 줄).  total ≈ 50-100 modules.
한 session 에 수 개 milestone 가능.

## Falsifiability checkpoints

각 phase 마 다 *예 상 막 힘* 위치 미리 marked:

- **B2 (negation)**: Raw 의 a/b swap 이 자연 한 가?  (이미 SwapLens
  존재)
- **B4 (division)**: positivity 의 *constructive* 형식 — Bishop 에
  서 도 까 다 로 움.
- **D3 (uniform continuity)**: framework-internal *compact* 정의 —
  ZFC compact 우회 의 핵심.
- **F3 (integration)**: 측 도 ⇒ 우 회 = Riemann 만.  Lebesgue 는
  measure theory 가 framework 에 부재 (별 도 큰 작업).
- **G3 (π)**: π 의 *constructive series* 는 가능 (Leibniz 또 는
  Wallis), 하 지 만 closed form 부재.

위 다 막 히 면 falsifiability — 어떤 phase 가 *영 구* 막 히 면
framework 폐기 (CLAUDE.md §1.5).

## ROI 의식

- Phase A-C 가 *foundation* — 이 까 지 가 가 장 important, 약 8-15 modules.
- Phase D-F 가 *core analysis* — 최 대 effort 投入.
- Phase G-H 가 *specific results* — 보 너 스, 필 요 시.

## Cross-references

- `notes/D1_zfc_real_as_final_boss.md` (retracted framing, valid evidence).
- `notes/D2_complexity_class_hierarchy.md` (Tier classification).
- `notes/D3_real213_native_R.md` (Real213 = native ℝ statement).
- `framework/E213/Research/Real213.lean`, `Real213Equiv.lean`,
  `Real213Const.lean` (Phase A 의 done parts).
- `framework/E213/Research/HasModulus.lean` (Bishop modulus
  infrastructure).
- `framework/E213/Research/PellHasModulus.lean` (concrete instance).
