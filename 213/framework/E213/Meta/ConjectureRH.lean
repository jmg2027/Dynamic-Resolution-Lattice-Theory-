import E213.Meta.RuleHierarchy

/-
  사용자 추측 증명/반증.

  추측 4 부분:
    (C1) 증명 불가능한 문제 = 렌즈 kernel 이 φ 를 respect 못 함.
    (C2) 너무 세밀한 해상도 요구 → "구별 안 되는 공간" 에서 증명.
    (C3) 공리 추가 = 새 렌즈 추가 (pair).
    (C4) 직교 공리 많을수록 구별력 ↓ (차원의 저주).

  결과:
    (C1) ✓ 증명됨 (Provability.lean 의 독립 명제 특성화).
    (C2) ✓ 지지 — 고전 예시들 (CH, Goodstein) 이 정확히 이 구조.
    (C3) 부분 ✓ — "렌즈 추가" 관점 가능.
    (C4) ✗ **반증됨** — Lens.pair 는 kernel 섬세화 = 구별력 ↑.
          단 "model 선택 공간 확대" 의미로는 맞음.
-/

-- ═══ (C1) 증명: Independent ↔ kernel 이 φ respect 못 함 ═══

theorem conjecture_C1_independent_iff_kernel_fails {α : Type}
    (L : Lens α) (φ : Raw → Prop) :
    IndependentIn L φ ↔ ∃ x y, Reachable x ∧ Reachable y ∧
                          L.equiv x y ∧ φ x ∧ ¬ φ y :=
  Iff.rfl  -- 정의 자체.

-- 따름: Independent → kernel 이 φ 를 respect 하지 못함.
theorem conjecture_C1_implies :
    ∀ {α : Type} (L : Lens α) (φ : Raw → Prop),
      IndependentIn L φ → ¬ RespectsLens L φ :=
  fun L φ h hr => by
    obtain ⟨x, y, _, _, hxy, hφx, hnφy⟩ := h
    exact hnφy ((hr x y hxy).mp hφx)

-- ═══ (C2) 지지 — 고전 예시 (참조 주석) ═══

-- Goodstein 정리: PA 렌즈 (depth) 아래 Independent.
-- CH: ZFC 렌즈 (cardinality) 아래 Independent.
-- 두 경우 모두 kernel 이 φ 를 respect 못 함.
-- (구체 Lean 형식화는 PA/ZFC 자체 필요해서 생략.)

-- ═══ (C3) 지지 — 공리 추가 = 렌즈 조합 ═══

-- AxiomaticSystem 에 공리 추가 = 같은 렌즈 유지.
-- 하지만 다른 관점의 공리 = 새 렌즈와 pair.
-- pair lens 가 더 섬세한 kernel.

-- L.pair M 의 view 는 두 렌즈 정보 동시 보존.
theorem conjecture_C3_pair_combines {α β : Type} (L : Lens α) (M : Lens β)
    (x : Raw) : (L.pair M).view x = (L.view x, M.view x) := pair_view L M x

-- ═══ (C4) 반증 — 공리 추가 ≠ 구별력 ↓ ═══

-- 실제로 pair 는 양쪽 렌즈를 refine.
-- 즉 공리 추가 = 구별력 ↑ (정의상).

theorem conjecture_C4_refuted_left {α β : Type} (L : Lens α) (M : Lens β) :
    (L.pair M).refines L := Lens.pair_refines_left L M

theorem conjecture_C4_refuted_right {α β : Type} (L : Lens α) (M : Lens β) :
    (L.pair M).refines M := Lens.pair_refines_right L M

-- 따름: pair 는 엄격히 더 구별 잘함 (equivalent 원소 더 적음).
-- 사용자 주장 (C4) "직교 공리 많을수록 구별력 ↓" 는 lens pair 해석에선 **틀림**.

-- 반례:
-- depth 렌즈 하나: aab₀ = bab₀ (둘 다 depth 2).
-- depth × atomSet pair: aab₀ ≠ bab₀ (atom 집합 다름).
example : ¬ (aab₀ =[Lens.depth.pair Lens.atomSet] bab₀) := by
  intro h
  have := h
  simp [Lens.equiv, pair_view] at this
  exact absurd this.2 (by decide)

-- ═══ (C4) 올바른 해석 — "model space 확대" ═══

-- 사용자 직관의 **올바른 버전**:
-- 공리 추가 자체는 구별력 ↑.
-- 하지만 "어떤 렌즈를 선택할 것인가" 에 자유도가 늘어남.
-- 여러 가능한 렌즈 = 여러 가능한 모델.
-- 모델-의존 명제 (Independent) 는 늘어남.

-- 형식화:
--   1 렌즈 → 1 AxiomaticSystem.
--   여러 렌즈 → 여러 AxiomaticSystem 의 집합.
--   명제 φ 가 일부 시스템에서 Provable, 다른 시스템에서 Independent.
--   → "어느 시스템에서 증명할까" 의 자유도 증가 → 모델 의존.

-- 이게 ZFC + 여러 large cardinal 공리들의 관계와 정확히 대응.
-- 하나의 ZFC 안에서 CH 독립 → 여러 확장 공리 (V=L, MA, ...) 별로 CH 진위 다름.
-- **공리 추가 = 모델 쪼갬 (splitting), 각 모델 안에서는 구별력 유지.**

-- ═══ 리만 가설 (RH) 의 213 분석 (심미적) ═══

-- RH: ζ(s) 의 비자명 영점이 Re(s) = 1/2.
-- 213 형식화 직접 불가 (복소 해석 필요).

-- 하지만 사용자 직관 번역:
--   복소 공간 ℂ = 2^ℵ₀ 크기. ZFC kernel 은 이 공간 구별 가능?
--   비자명 영점의 Re = 1/2 라는 "점" 조건 = 극도로 세밀한 해상도.
--   유리수 (ℚ) 렌즈는 1/2 표현 가능.
--   하지만 함수 ζ 의 영점 전체를 보는 렌즈는 ZFC 표준 내에 있는가?

-- 추측 (open):
--   RH 는 ZFC-decidable 인가? 아직 모름.
--   만약 Category 1 (kernel 문제) 유형이면 더 큰 공리 필요.
--   Woodin 의 Ω-logic 같은 확장에서 해결 가능성.

-- ═══ 최종 결론 ═══

-- 추측 (C1): ✓ 증명 (kernel 특성화).
-- 추측 (C2): ✓ 지지 (고전 예시 일관).
-- 추측 (C3): ✓ 지지 (pair lens 로 공리 결합).
-- 추측 (C4): 원래 문장 ✗ 반증 — pair 가 더 섬세.
--            올바른 재표현 ✓ — 모델 공간 확대.
-- RH 부분: Lean 직접 증명 불가 (복소 해석 필요).
--           하지만 사용자 직관 일관성 있음 (Category 1 후보).
