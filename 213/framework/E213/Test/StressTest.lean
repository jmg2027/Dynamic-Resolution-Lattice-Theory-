import E213.Firmware.Axiom
import E213.Firmware.Closure

/-
  Firmware 테스트 4: 경계/스트레스.
  큰 입력, 깊은 Obj, pairs 큰 값, chain 깊이.
-/

-- ═══ T1: pairs 큰 값 ═══
theorem s1_p100 : pairs 100 = 4950 := by native_decide
theorem s1_p1000 : pairs 1000 = 499500 := by native_decide

-- 자기유지가 3뿐임을 큰 범위에서 확인:
theorem s1_unique :
    (List.range 200).filter (fun n => n > 0 && pairs n == n)
    = [3] := by native_decide

-- ═══ T2: Obj depth 스트레스 ═══

-- 깊이 10인 Obj:
def deepObj : Nat → Obj
  | 0 => .gen 0
  | n+1 => .mul (deepObj n) (.gen 1)

-- depth 확인:
theorem s2_d0 : (deepObj 0).depth = 0 := by native_decide
theorem s2_d1 : (deepObj 1).depth = 1 := by native_decide
theorem s2_d5 : (deepObj 5).depth = 5 := by native_decide
theorem s2_d10 : (deepObj 10).depth = 10 := by native_decide

-- leaves 확인:
theorem s2_l1 : (deepObj 0).leaves = 1 := by native_decide
theorem s2_l5 : (deepObj 4).leaves = 5 := by native_decide
theorem s2_l10 : (deepObj 9).leaves = 10 := by native_decide

-- 모두 Generated:
theorem s2_gen5 : Generated (deepObj 5) := all_generated _
theorem s2_gen10 : Generated (deepObj 10) := all_generated _

-- ═══ T3: 큰 chain ═══

-- chain 10번, mod 7:
def addM7 (a b : Nat) : Nat := (a + b) % 7
def t7 : Triple Nat := ⟨0, 1, 2⟩

-- 주기 찾기:
#eval (List.range 20).map fun k =>
  (chain addM7 t7 k).x

-- 주기가 존재함 (유한 공간이므로 필연).

-- ═══ T4: 폭발 체인 추적 ═══

-- pairs를 반복 적용하면 얼마나 빨리 폭발?
def iterP : Nat → Nat → Nat
  | 0, n => n
  | k+1, n => iterP k (pairs n)

#eval (List.range 6).map (iterP · 4)
-- [4, 6, 15, 105, 5460, ...] 급격 폭발!

#eval (List.range 6).map (iterP · 3)
-- [3, 3, 3, 3, 3, 3] 영원히 안정!

-- ═══ T5: 붕괴 체인 추적 ═══
#eval (List.range 6).map (iterP · 2)
-- [2, 1, 0, 0, 0, 0] 즉시 소멸!

#eval (List.range 6).map (iterP · 1)
-- [1, 0, 0, 0, 0, 0]

-- ═══ 결론 ═══
-- n=3만 안정. n<3 붕괴. n>3 폭발. firmware 정상.
