import E213.Firmware.Axiom
import E213.Firmware.Closure
import E213.Firmware.PairInTriple
import E213.Firmware.Profile

/-
  Firmware 테스트 2: ISA 제약 조건.
  자기유지(3), 붕괴(≤2), 폭발(≥4), pair⊂triple, 접속행렬.
-/

-- ═══ T1: 자기유지 = 3만 ═══
theorem c1_only3 :
    (List.range 100).filter (fun n => n > 0 && pairs n == n)
    = [3] := by native_decide

-- ═══ T2: 붕괴 체인 ═══
-- n=2: 2 → 1 → 0. 소멸.
theorem c2_chain : pairs 2 = 1 ∧ pairs 1 = 0 ∧ pairs 0 = 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

-- n=1: 즉시 소멸.
theorem c2_instant : pairs 1 = 0 := by native_decide

-- ═══ T3: 폭발 체인 ═══
-- n=4: 4 → 6 → 15 → 105 → ...
theorem c3_explode :
    pairs 4 = 6 ∧ pairs 6 = 15 ∧ pairs 15 = 105 := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

-- ═══ T4: 안정 체인 ═══
-- n=3: 3 → 3 → 3 → ... 영원히.
theorem c4_stable :
    pairs 3 = 3 ∧ pairs (pairs 3) = 3 ∧
    pairs (pairs (pairs 3)) = 3 := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

-- ═══ T5: pair_in_triple ═══
-- 임의의 두 Obj에 대해 triple 존재.
theorem c5_pair (a b : Obj) :
    ∃ c, Generated (.mul a b) ∧ Generated (.mul a c) ∧
         Generated (.mul b c) :=
  pair_in_triple a b

-- 구체적 예:
theorem c5_concrete :
    ∃ c, Generated (.mul (.gen 0) (.gen 1)) ∧
         Generated (.mul (.gen 0) c) ∧
         Generated (.mul (.gen 1) c) :=
  pair_in_triple (.gen 0) (.gen 1)

-- ═══ T6: 접속 행렬 ═══
-- n=2: 행 동일 → 구분 불가.
theorem c6_same : inc2 0 = inc2 1 := by native_decide
-- n=3: 행 전부 다름 → 구분 가능.
theorem c6_diff : inc3 0 ≠ inc3 1 ∧ inc3 0 ≠ inc3 2 ∧
    inc3 1 ≠ inc3 2 := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

-- ═══ T7: 방향 = 2 ═══
theorem c7_dirs :
    ((List.range 6).filter fun k => choose 3 k > 1) = [1, 2] := by
  native_decide
