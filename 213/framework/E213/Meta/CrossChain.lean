import E213.Meta.Patterns

/-
  Cross-chain: 여러 공리계를 연결하는 정리.

  관찰: 같은 Raw 가 다른 공리계에서 다른 의미.
  예:
    a₀ (atom 0) = Peano.zero = Logic.⊤ = Set.∅ = Algebra.0 = SST.+1.
    같은 Raw, 5 개의 의미.
  이게 213 의 "한 바닥, 여러 해석" 구조.

  Cross-chain 정리:
    한 공리계의 사실이 다른 공리계에서 어떤 의미인지.
    Lens 전환 bridge.
-/

-- ═══ a₀ 의 5가지 해석 ═══

-- CC_001: Peano 관점 — a₀ 는 zero.
theorem cc_001_peano : Nat213.zero.toRaw = a₀ := rfl

-- CC_002: Logic 관점 — a₀ 는 ⊤.
theorem cc_002_logic : Prop213.tru.toRaw = a₀ := rfl

-- CC_003: Set 관점 — a₀ 는 ∅.
theorem cc_003_set : emptySet = a₀ := rfl

-- CC_004: Algebra 관점 — a₀ 는 Z3 원소 0.
theorem cc_004_algebra : Lens.Z3.view a₀ = ⟨0, by decide⟩ := by decide

-- CC_005: SST 관점 — a₀ 는 +1 (양성).
theorem cc_005_sst : Lens.signed.view a₀ = 1 := by decide

-- 같은 Raw, 5 해석.

-- ═══ b₀ 의 4가지 해석 ═══

-- CC_006: Logic 관점 — b₀ 는 ⊥.
theorem cc_006_logic : Prop213.fls.toRaw = b₀ := rfl

-- CC_007: Algebra 관점 — b₀ 는 Z3 원소 1.
theorem cc_007_algebra : Lens.Z3.view b₀ = ⟨1, by decide⟩ := by decide

-- CC_008: SST 관점 — b₀ 는 -1 (음성).
theorem cc_008_sst : Lens.signed.view b₀ = -1 := by decide

-- ═══ rel 구조의 cross-chain 해석 ═══

-- ab₀ = rel a₀ b₀ 은:
--   Peano: zero 와 다른 뭔가 (Nat213 encoding 밖).
--   Logic: ⊤ → ⊥ = ⊥.
--   Set: {b₀} (atomSet 기준).
--   Algebra: Z3 0+1 = 1.
--   SST: 1 - (-1) = 2.

-- CC_009: Logic ab₀ 해석.
theorem cc_009 : Lens.truthValue.view ab₀ = false := by decide

-- CC_010: Algebra ab₀ 해석.
theorem cc_010 : Lens.Z3.view ab₀ = ⟨1, by decide⟩ := by decide

-- CC_011: SST ab₀ 해석.
theorem cc_011 : Lens.signed.view ab₀ = 2 := by decide

-- ═══ 한 명제의 다중 공리계 검증 ═══

-- 명제: "x 는 Reachable."
-- 같은 명제가 모든 공리계에서 의미 동일.

-- CC_012: Nat213 elements 는 Reachable.
theorem cc_012 (n : Nat213) : Reachable n.toRaw :=
  Nat213.toRaw_reachable n

-- CC_013: Prop213 elements 는 Reachable 일 수도 아닐 수도.
-- Prop213.imp tru tru → rel a₀ a₀ (Reachable 아님).
theorem cc_013 : ¬ Reachable (Prop213.imp .tru .tru).toRaw := by decide

-- 의미: 같은 "명제" 가 공리계에 따라 valid/invalid.
-- Logic 에서는 의미 있지만 Peano-style 에선 Reachable 조건에 걸림.

-- ═══ Bridge theorem: 공리계 전환 ═══

-- Peano zero → Logic ⊤ bridge.
-- 둘 다 같은 Raw (a₀) 로 encode.
theorem cc_014_peano_to_logic :
    Nat213.zero.toRaw = Prop213.tru.toRaw := rfl

-- Logic ⊥ → Set element bridge.
-- Prop213.fls.toRaw = b₀ 이 Set 의 원소.
theorem cc_015_logic_to_set :
    Prop213.fls.toRaw = b₀ := rfl

-- Algebra 0 → SST +1 bridge.
-- Z3 원소 0 = Raw 의 a₀ = SST 에서 +1.
theorem cc_016_algebra_to_sst :
    Lens.signed.view a₀ = 1 ∧ Lens.Z3.view a₀ = ⟨0, by decide⟩ := by
  refine ⟨?_, ?_⟩ <;> decide

-- ═══ 공리계 합의/불일치 ═══

-- 합의: 공리계 전체가 한 Raw 에 대해 같은 판정.
-- 불일치: 한 공리계 valid, 다른 것 invalid.

-- CC_017: a₀ 는 모든 공리계에서 Reachable.
theorem cc_017 : Reachable a₀ := .atom 0

-- CC_018: rel a₀ a₀ 은 어느 공리계에서든 Reachable 아님.
theorem cc_018 : ¬ Reachable (Raw.rel a₀ a₀) := by decide

-- 의미: Reachable 은 공리계 불변 (Firmware 수준).
-- 반면 "의미" (값) 는 렌즈 의존.
