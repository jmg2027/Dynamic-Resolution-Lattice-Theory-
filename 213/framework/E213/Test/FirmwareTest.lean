import E213.Firmware.Axiom
import E213.Firmware.Closure
import E213.Firmware.Negation

/-
  Firmware 테스트 1: Triple, relify, chain, pairs, Obj.
-/

-- ═══ T1: Triple 생성 ═══
def t : Triple Nat := ⟨10, 20, 30⟩
#eval t.x  -- 10

-- ═══ T2: relify 동작 ═══
#eval (relify (· + ·) t).x  -- 30 (10+20)
#eval (relify (· + ·) t).y  -- 40 (10+30)
#eval (relify (· + ·) t).z  -- 50 (20+30)
#eval (relify (· * ·) t).x  -- 200
#eval (relify Nat.min t).x  -- 10

-- ═══ T3: chain = relify 반복 ═══
theorem t3_chain0 : chain (· + ·) t 0 = t := rfl
theorem t3_chain1 : chain (· + ·) t 1 = relify (· + ·) t := rfl
#eval (chain (· + ·) t 0).x  -- 10
#eval (chain (· + ·) t 1).x  -- 30
#eval (chain (· + ·) t 2).x  -- 70

-- ═══ T4: pairs (C(n,2)) ═══
theorem t4_p0 : pairs 0 = 0 := by native_decide
theorem t4_p1 : pairs 1 = 0 := by native_decide
theorem t4_p2 : pairs 2 = 1 := by native_decide
theorem t4_p3 : pairs 3 = 3 := by native_decide
theorem t4_p5 : pairs 5 = 10 := by native_decide
theorem t4_p10 : pairs 10 = 45 := by native_decide

-- ═══ T5: Obj depth/leaves ═══
def oa : Obj := .gen 0
def oab : Obj := .mul (.gen 0) (.gen 1)
def oabc : Obj := .mul (.mul (.gen 0) (.gen 1)) (.gen 2)

theorem t5_d0 : oa.depth = 0 := by native_decide
theorem t5_d1 : oab.depth = 1 := by native_decide
theorem t5_d2 : oabc.depth = 2 := by native_decide
theorem t5_l1 : oa.leaves = 1 := by native_decide
theorem t5_l2 : oab.leaves = 2 := by native_decide
theorem t5_l3 : oabc.leaves = 3 := by native_decide

-- ═══ T6: all_generated ═══
theorem t6_a : Generated oa := all_generated _
theorem t6_ab : Generated oab := all_generated _
theorem t6_abc : Generated oabc := all_generated _
theorem t6_deep : Generated (.mul (.mul (.mul (.gen 0) (.gen 1))
    (.gen 2)) (.mul (.gen 0) (.gen 1))) := all_generated _

-- ═══ T7: no_third_constructor ═══
theorem t7_gen : (∃ i, oa = .gen i) ∨ (∃ a b, oa = .mul a b) :=
  no_third_constructor oa
theorem t7_mul : (∃ i, oab = .gen i) ∨ (∃ a b, oab = .mul a b) :=
  no_third_constructor oab
