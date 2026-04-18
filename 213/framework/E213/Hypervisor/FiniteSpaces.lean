import E213.Firmware.Axiom

/-
  213을 담는 유한 공간.
  chain은 유한 공간에서 순환 (비둘기집).
  비축소 순환이 가능한가? → 𝔽₃ + 덧셈: 가능.
-/

def Triple.vals (t : Triple α) : α × α × α := (t.x, t.y, t.z)

-- ═══ 𝔽₃, 덧셈: 최소 성공 ═══

def add3 (a b : Fin 3) : Fin 3 := ⟨(a.val + b.val) % 3, by omega⟩
def t0f3 : Triple (Fin 3) := ⟨0, 1, 2⟩

#eval (chain add3 t0f3 0).vals  -- (0, 1, 2)
#eval (chain add3 t0f3 1).vals  -- (1, 2, 0) 순열!
#eval (chain add3 t0f3 2).vals  -- (0, 1, 2) 주기 2!

def distinct3 (t : Triple (Fin 3)) : Bool :=
  decide (t.x ≠ t.y) && decide (t.x ≠ t.z) && decide (t.y ≠ t.z)

-- 비축소: 세 원소 항상 다름.
theorem f3_noncollapse :
    distinct3 t0f3 = true ∧
    distinct3 (chain add3 t0f3 1) = true := by
  constructor <;> native_decide

-- 주기 = 2.
theorem f3_period :
    (chain add3 t0f3 2).vals = t0f3.vals := by native_decide

-- ═══ 𝔽₃, 곱셈: 실패 ═══

def mul3 (a b : Fin 3) : Fin 3 := ⟨(a.val * b.val) % 3, by omega⟩

-- 0이 흡수원: 0×a = 0. 축소.
theorem mul_collapse :
    distinct3 (relify mul3 t0f3) = false := by native_decide

-- ═══ ℤ/5ℤ, 덧셈: 주기 4 ═══

def add5 (a b : Fin 5) : Fin 5 := ⟨(a.val + b.val) % 5, by omega⟩
def t0f5 : Triple (Fin 5) := ⟨0, 1, 2⟩

#eval (chain add5 t0f5 0).vals  -- (0, 1, 2)
#eval (chain add5 t0f5 1).vals  -- (1, 2, 3)
#eval (chain add5 t0f5 2).vals  -- (3, 4, 0)
#eval (chain add5 t0f5 3).vals  -- (2, 3, 4)
#eval (chain add5 t0f5 4).vals  -- (0, 1, 2) 주기 4!

-- ═══ 주기 = 해상도 ═══
-- 𝔽₃: 주기 2. 최소 해상도. 2번 비교하면 원래로.
-- ℤ/5ℤ: 주기 4. 중간 해상도.
-- ℂ: 주기 ∞ (일반적). 무한 해상도.
-- = 은 "주기만큼 비교하면 원래로" = 그 이상 구분 불가.
-- 주기 = Arithmetic.lean의 "= 이 해상도 의존"의 구체적 실현.

-- ═══ 213을 담는 조건 ═══
-- 1. |S| ≥ 3 (Triple 구성 가능).
-- 2. × 교환적 (대칭 비교).
-- 3. relify 비축소 (distinct 유지).
-- 4. 최소: 𝔽₃. 𝔽₂는 |S|=2로 부족.

-- ═══ 요약 ═══
structure FiniteSpaceResult where
  f3_works : distinct3 t0f3 = true ∧
             distinct3 (chain add3 t0f3 1) = true
  period_2 : (chain add3 t0f3 2).vals = t0f3.vals
  mul_fails : distinct3 (relify mul3 t0f3) = false

theorem finite_spaces : FiniteSpaceResult where
  f3_works := ⟨by native_decide, by native_decide⟩
  period_2 := by native_decide
  mul_fails := by native_decide
