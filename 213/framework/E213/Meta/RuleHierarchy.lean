import E213.Meta.LimitsOfMeta

/-
  Rule Hierarchy: 무한을 만드는 규칙의 계단.

  관찰: 213의 무한은 유한한 규칙들에서 나온다.
  그 규칙을 하나씩 제거 하면 계단을 내려가 유한 으로 수렴.
  Cayley-Dickson 과 유사한 계층 구조.

  213 의 "무한 생성 규칙" (6개):
    R1. Labeled atoms (Fin n, n ≥ 2).
    R2. Binary operation (rel x y).
    R3. Recursion (Raw → Raw → Raw, 자기 적용).
    R4. Injectivity (rel x y 고유).
    R5. Anti-reflexivity (x ≠ y 제약).
    R6. Decidability (DecidableEq, 기계적 판정).

  각 규칙 하나씩 제거 → 공간 점진적 축소.
  결정적 지점: R3 (recursion) 제거 시 즉시 유한.

  Cayley-Dickson 평행:
    ℝ → ℂ → ℍ → 𝕆 → 𝕊 → 32-ion → ... → 의미 상실.
    각 단계마다 대수 규칙 하나씩 소실.
    16원수 이상에서 "의미 없는" 공간.

  213 에서의 대응:
    Level 0: 모든 규칙. 무한 + 구조 있음.
    Level 3: recursion 소실. 유한으로 붕괴.
    Level 6: 모든 규칙 소실. 단일 점 또는 Empty.
-/

-- ═══ Level 0: Full 213 ═══

-- 현재 Raw 가 이것. 모든 규칙 보존.
-- Reachable + 6 규칙.
-- Cardinality: ℵ₀.

example : ∃ x : Raw, True := ⟨a₀, trivial⟩
-- Raw는 무한: raw_has_arbitrary_depth.

-- ═══ Level 1: R5 제거 (anti-reflexivity) ═══

-- rel x x 허용. 즉 Reachable 조건 포기.
-- Type 은 그대로 Raw. 다만 모든 Raw (유령 포함) 인정.
-- Cardinality: 여전히 ℵ₀. 구조 덜 제약.

example : ∃ x : Raw, x = Raw.rel a₀ a₀ := ⟨Raw.rel a₀ a₀, rfl⟩
-- atom self-pair 가능. Reachable 조건 밖.

-- ═══ Level 2: R4 제거 (injectivity) ═══

-- rel 가 단사 아닐 수 있는 구조.
-- Quotient 로 표현: Raw / (~ where rel x y ~ rel y x).
-- Cardinality: ≤ ℵ₀ (quotient class).

-- 형식화: Raw/~ type where ~ is any equivalence.
def Level2Raw : Type := Quotient (inferInstance : Setoid Raw)
-- 기본 Setoid 는 =. 이걸 약한 relation 으로 바꿀 수 있음.
-- 여기선 abstract. 실제 relation 지정해 quotient.

-- ═══ Level 3: R3 제거 (recursion) ═══

-- rel 을 한 번만 적용. 재귀 금지.
-- Type: Fin 3 ⊕ (Fin 3 × Fin 3).
-- Cardinality: 3 + 9 = 12 (유한!).

def Level3Raw : Type := Fin 3 ⊕ (Fin 3 × Fin 3)

instance : Fintype Level3Raw := inferInstance

theorem level3_finite : Fintype.card Level3Raw = 12 := by decide

-- **무한 → 유한 전이의 결정적 지점.**
-- Recursion 없으면 즉시 유한.

-- ═══ Level 4: R2 제거 (binary) ═══

-- rel 아예 없음. atoms only.
-- Type: Fin 3.
-- Cardinality: 3.

def Level4Raw : Type := Fin 3
theorem level4_card : Fintype.card Level4Raw = 3 := by decide

-- ═══ Level 5: R1 제거 (labels) ═══

-- Atoms 구별 없음. 1 점.
-- Type: Unit.
-- Cardinality: 1.

def Level5Raw : Type := Unit
theorem level5_card : Fintype.card Level5Raw = 1 := by decide

-- ═══ Level 6: R6 제거 (decidability) ═══

-- 원소 자체 없음.
-- Type: Empty.
-- Cardinality: 0.

def Level6Raw : Type := Empty
theorem level6_card : Fintype.card Level6Raw = 0 := by decide

-- ═══ 계단 요약 ═══

-- | Level | 제거 규칙         | Type              | Card | 무한? |
-- |-------|-----------------|-------------------|------|-------|
-- | 0     | (모두 있음)       | Reachable         | ℵ₀   | ✓     |
-- | 1     | R5 (anti-refl)  | Raw (유령 포함)    | ℵ₀   | ✓     |
-- | 2     | R4 (inj)        | Raw / ~           | ≤ℵ₀  | 가능  |
-- | 3     | R3 (recursion)  | Fin 3 ⊕ Fin 3×3   | 12   | ✗ ★  |
-- | 4     | R2 (binary)     | Fin 3             | 3    | ✗     |
-- | 5     | R1 (labels)     | Unit              | 1    | ✗     |
-- | 6     | R6 (decidable)  | Empty             | 0    | ✗     |

-- ═══ 결정적 지점 ═══

-- ★ Level 3 (recursion 제거): **무한 → 유한 단번에.**
-- 다른 어떤 규칙 제거도 단계적 축소만 유발.
-- Recursion 이 유일한 "무한 생산" 규칙.

-- Cayley-Dickson 평행:
--   ℝ (8규칙) → ... → 32-ion → 의미 없음.
--   213 (6규칙) → Level 3 에서 cliff → 유한.

-- ═══ 의미 상실 시점 ═══

-- Level 0-2: 무한, 구조 풍부 (의미 있음).
-- Level 3: 유한 12개, 구조 여전.
-- Level 4: 유한 3, trivial algebra.
-- Level 5: 1점, 모든 것 동일.
-- Level 6: Empty, **논리적으로 의미 없는 공간**.

-- 결론:
--   무한 만드는 규칙 = 6개 (유한 list).
--   Recursion (R3) 이 본질적 원천.
--   규칙 소진 시 Empty 로 붕괴.
--   완전 의미 상실 지점 = Level 6 (Empty).
