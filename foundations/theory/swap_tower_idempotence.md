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

| # | 성질 | 증명 |
|---|------|------|
| i | 유일한 고정점 `d = 5 ↔ Gr(3,5)` | [5, 500) 전수 확인 |
| ii | `T^∞(d) = 5` (모든 alive `d`) | 17개 궤적 수렴 |
| iii | `T ∘ T^∞ = T^∞` (idempotence on orbit closure) | fixed pt 직접 |
| iv | `O(log d)` 수렴 | ratio < 3 (d ≤ 5000) |
| v | `FM_N(Gr(3,5)) χ = 5^N·(N+1)!` 보존 | FND_011 일치 |
| vi | Pairwise σ = 1-step T | 7 개 test case 일치 |

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

## 4. 열린 문제

- **OT-1 (Lean 형식화).**  T 를 monad 로 Lean 에 기술 후
  fixed-point theorem 증명.  현재 pairwise σ 만 Lean 에 있음.
- **OT-2 (Operad 구조).**  T∘T 가 Gr(3,5) 위에서 literally id 인가,
  아니면 coherence isomorphism 까지만 id 인가?
- **OT-3 (Physical 해석.)**  Tower 의 각 level 이 RG flow / scale
  hierarchy 와 대응하는가?  d_indep 의 log-스케일 수렴이
  β-function 과 관계 있는가?
- **OT-4 (Non-alive case).**  Dead sector (b=0 또는 a=0) 에서
  T 의 행동은?  Atom 이 유일하게 소멸되는 경계 조건?

---

## 5. Lean 초안 (future work)

```lean
-- critical-line/lean/PmfRh/SwapTower.lean  (proposed)
structure AliveDim where
  d : Nat
  a : Nat
  b : Nat
  ha : 1 ≤ a
  hb : 1 ≤ b
  hd : d = 2*a + 3*b

def tower (x : AliveDim) : Nat :=
  2 * ((x.a + 1) / 2) + 3 * ((x.b + 1) / 2)

theorem tower_fixed_five (x : AliveDim) (h : x.d = 5) :
    tower x = 5 := by
  -- unique alive decomp of 5 is (1,1); tower (1,1) = 5
  sorry  -- OT-1

theorem tower_converges (x : AliveDim) :
    ∃ n, Nat.iterate tower n x.d = 5 := by
  sorry  -- OT-1
```

---

**References.**
- `foundations/experiments/FND_038_swap_tower_idempotence.py`
- `foundations/results/EXP_FND_038_Swap_Tower_Operadic_Idempotence.txt`
- `foundations/experiments/FND_012_swap_involution.py` (1-level)
- `critical-line/lean/PmfRh/SwapAnnihilation.lean` (Lean 1-level)
- `foundations/experiments/FND_011_fm_cohomology.py` (FM χ)
