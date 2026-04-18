# Swap Tower = Operadic Idempotence

**Status:** (A) verified (FND_038, 9/9 checks).
**Extends:** FND_012 (pairwise σ, Grassmannian involution),
`critical-line/lean/PmfRh/SwapAnnihilation.lean`.
**Source intuition:** Mingu Jeong (2026-04-18):

> "N점이 있을 때 N개의 심플렉스, 각 꼭지점에 또 심플렉스,
> 또 각 꼭지점에 심플렉스... 이게 swap annihilation 아닐까?"

---

## 1. 구조

**Pairwise view (기존, FND_012 / SwapAnnihilation.lean).**
`(a,a)` 반복 block 위에서 외부 자기동형
`σ: (g₁,g₂) ↦ (g₂,g₁)`. σ-고정 sector의 차원
`d_indep(a,b) = 2⌈a/2⌉ + 3⌈b/2⌉`.
*1 level만 본 그림.*

**Tower view (사용자 직관, FND_038).**
심플렉스의 각 꼭지점에 또 심플렉스를 매다는 함자
`T: Simp → Simp`.  Alive 차원 `d = 2a+3b` (a,b ≥ 1) 위에서
`T(d) := d_indep(a,b)`  (canonical minimal-b decomp).
*무한 재귀 탑 — pairwise σ를 반복 적용.*

두 view의 관계:
```
pairwise σ  =  T 를 1 level restriction
tower T     =  σ 를 monad/operad 로 올린 것
```

---

## 2. 정리 (FND_038)

`T`는 다음을 만족한다:

| # | 성질 | Python (FND_038) | Lean (SwapTower.lean) |
|---|------|------------------|------------------------|
| i | 유일한 고정점 `d = 5 ↔ Gr(3,5)` | [5, 500) 전수 | `fixed_iff_five` |
| ii | `T^∞(d) = 5` (모든 alive `d`) | 17 궤적 | `tower_decreases_to_five` |
| iii | `T ∘ T^∞ = T^∞` | fixed pt 직접 | `base_is_fixed` |
| iv | `O(log d)` 수렴 | ratio < 3 | (암시: strict decrease) |
| v | `FM_N(Gr(3,5)) χ = 5^N·(N+1)!` 보존 | FND_011 | — (comment only) |
| vi | Pairwise σ = 1-step T | 7 test | `pairwise_is_tower` (rfl) |
| vii | Strict decrease off d=5 (OT-2) | 12 d 값 | `tower_strict_off_five` |
| viii | Dead sector stability (OT-4) | 8 d 값 | `dead_sector_closed` |
| ix | Dead → alive 벽 (OT-4) | `T_dead ≠ 5` | `dead_tower_ne_five` |
| x | alive/dead dim 중첩 (OT-4) | (3,1)↔(0,3)=9 | `alive_dead_dims_can_coincide` |

**따름정리 (user intuition 검증됨):**
Swap annihilation = 중첩된 심플렉스 탑의 (3,2) atomic pair 로의
재귀적 붕괴.  `ch02 / SwapAnnihilation.lean` 의 pairwise σ 는
simplex tower 위의 operadic monad `T` 의 1-level slice.

---

## 3. 왜 중요한가

1. **Algebraic priority 준수.** T 의 고정점은 연속 변분/피팅이
   아니라 **counting + iteration** 에서 나옴.  CLAUDE.md 의
   "결과는 세기에서" 원칙 부합.

2. **기존 결과 자연 흡수.**
   - FND_011 (FM χ) = T 의 한 level bubble cardinality.
   - FND_012 (pairwise σ) = T 의 1-level restriction.
   - FND_017 (tensor fractal tower) = T 의 Schur–Weyl 표현론.
   - FND_030–033 (scale-inv ⟺ confluence) = T 의 monadic
     associativity 의 범주론적 재진술.

3. **Self-reference 가 구조화됨.**
   FND_012 결과 154–157 줄의 관찰 ("Gr(3,5) is fixed point of
   the swap operation") 이 이제 정리 (i) 로 포함됨.

4. **왜 d=5 유일인가 의 또 다른 경로.**
   - Path A (ch02): atoms {2,3} + alive + unique decomp
   - Path B (FND_033): γ' operator, unique-decomp criterion
   - **Path C (FND_038): T 의 유일 고정점 = counting iteration**

---

## 4. 열린 문제 — 현재 상태

- **OT-1 (Lean 형식화).** ✅ **CLOSED.**
  `critical-line/lean/PmfRh/SwapTower.lean`, 15 theorems, 0 sorry.
  `AliveDim`, `towerStep`, `fixed_implies_five`, `fixed_iff_five`
  등 포함.  전체 PmfRh 빌드 성공 (2727 모듈).

- **OT-2 (Operad idempotence, strict).** ✅ **CLOSED.**
  `tower_strict_off_five` : `5 < x.dim → towerStep x < x.dim`.
  `tower_decreases_to_five` : 비증가 + equality iff fixed.
  => T 반복은 절대 정체되지 않고 유한 step 내 고정점 도달.
  이는 monad μ : T² → T 의 **strict idempotence** on orbit closure.
  Weak (∞-categorical coherence) 버전은 여전히 탐구 대상.

- **OT-3 (Physical 해석.)** 열려 있음.
  `O(log d)` 수렴 (FND_038 Check 4) 이 β-function 이나 RG scale
  hierarchy 와 대응하는가?  현재는 순수 이산 구조로, 연속
  대응은 미탐구.

- **OT-4 (Dead sector).** ✅ **CLOSED (structural).**
  `DeadDim` (a=0 ∨ b=0) 형식화:
  - `dead_sector_closed`: missing atom 은 반복 후에도 missing
  - `dead_tower_ne_five`: dead 출력은 절대 5 가 아님 (alive 벽)
  - `alive_dead_dims_can_coincide`: alive (3,1) 과 dead (0,3)
    둘 다 dim=9 — **차원만으로는 alive/dead 구분 불가**.
    구분은 STRUCTURAL (어느 atom 이 쌍으로 있는가) 이지
    dimensional 아님.  Book 의 "v ≥ 6 ambiguity" 와 정확히 부합.

### OT-4 의 개념적 함의

Alive/dead 차원이 겹칠 수 있다는 사실은 **atom 구조 (어느 원자가
쌍으로 존재하는가) 가 차원보다 더 근본적인 invariant** 임을 보여준다.
이는 ch02 의 "chiral decomposition 은 atoms 자체로 주어진다"
주장의 구체적 실현.  d=5 의 유일성이 차원 counting 이 아니라
(3,2) 원자 쌍의 유일성에서 오는 이유이기도 하다.

---

## 5. Lean 현황 (실제 구현)

`critical-line/lean/PmfRh/SwapTower.lean` — 15 theorems, 0 sorry.
빌드 확인됨 (2727 모듈 전체 통과).

주요 정리:
- `AliveDim`, `DeadDim` 구조체
- `towerStep`, `deadTowerStep`, `dIndep`
- `fixed_implies_five`, `fixed_iff_five`
- `tower_strict_off_five`, `tower_decreases_to_five`
- `dead_sector_closed`, `dead_tower_ne_five`
- `alive_dead_dims_can_coincide`
- `pairwise_is_tower` (definitional: `rfl`)

모든 증명은 순수 Nat + `omega` (Mathlib 대수 의존성 없음).

---

**References.**
- `foundations/experiments/FND_038_swap_tower_idempotence.py` (12/12 ✓)
- `foundations/results/EXP_FND_038_Swap_Tower_Operadic_Idempotence.txt`
- `foundations/experiments/FND_012_swap_involution.py` (1-level)
- `critical-line/lean/PmfRh/SwapTower.lean` (Lean formalization)
- `critical-line/lean/PmfRh/SwapAnnihilation.lean` (Lean 1-level)
- `foundations/experiments/FND_011_fm_cohomology.py` (FM χ)
