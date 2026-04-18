import E213.Meta.ConjectureRH

/-
  차원 저주: 구별 능력의 이중성.

  사용자 지적: "Span 하는 차원 늘어날수록 구별 불가능."

  내가 놓친 것: **"구별"의 두 의미.**

  (A) Boolean 구별 (mathematical distinguishability):
      pair lens 가 엄격히 더 섬세. 구별력 ↑.
      이게 이전 증명한 것 (pair_refines).

  (B) 밀도-기반 구별 (statistical distinguishability):
      Joint image 가 product 로 확대 → 각 class 당 밀도 ↓.
      차원 저주 (curse of dimensionality).
      이게 사용자가 의미한 것.

  두 현상 양립:
    pair kernel ⊆ L kernel  (정의상, Boolean).
    |pair image| ≥ |L image|  (product, density).
    개별 class 크기 ↓ but class 수 ↑.
-/

-- ═══ (A) Boolean: pair 더 섬세 ═══

-- 이미 증명됨 (Meta/Category.lean):
--   pair_refines_left, pair_refines_right.

example (L : Lens Nat) (M : Lens Nat) :
    (L.pair M).refines L := Lens.pair_refines_left _ _

-- ═══ (B) Density: joint image 는 product 공간 ═══

-- L.pair M 의 view = (L.view, M.view). 즉 joint image ⊆ α × β.
-- 개별 Raw 하나는 한 (a, b) 좌표.
-- |Raw| = ℵ₀ 가 α × β 공간에 분포.
-- α × β 가 α 보다 크면 class 당 밀도 ↓.

-- 정량화: |joint image| ≥ max(|L image|, |M image|).
-- 각 dim 은 marginal 유지.
-- 하지만 joint 는 product 크기까지 확대 가능.

-- 구체 예: Raw Level 2 = 75 원소.
-- depth 렌즈: image ⊆ {0, 1, 2, 3} (Level 2 내). 4 values.
-- leaves 렌즈: image ⊆ {1, 2, 3, 4}. 4 values.
-- pair: image ⊆ {0..3} × {1..4}. 최대 16 positions.
-- 평균 75/16 ≈ 4.7 Raw per cell.
-- 75/4 ≈ 18.75 Raw per depth class.
-- 밀도 4배 감소.

-- ═══ 결론: 두 주장 양립 ═══

-- (A) "공리 추가 = 더 섬세 kernel": ✓ (pair_refines).
-- (B) "공리 추가 = 차원 저주": ✓ (joint image 확대).
-- 수학적 섬세도와 통계적 밀도는 **다른 양**.

-- 사용자 주장의 올바른 형식:
--   많은 공리 = joint image 지수적 확대.
--   각 joint class 의 Raw 밀도 지수적 감소.
--   → **"어떤 class 에서 의미 있는 진술"** 이 어려워짐.
--   → "구별은 가능, 하지만 sparse."

-- 이게 차원 저주의 213 버전.

-- 수학 분야 적용:
-- ZFC + 많은 large cardinal 공리:
--   각 조합이 다른 모델.
--   모델 공간 확대 → 각 모델 분포 sparse.
--   명제의 진위가 모델 의존 → 많은 Independent.
--   이게 "구별 불가능" 의 실제 의미.

-- ═══ Lean 추가 정리 ═══

-- Marginal 정보 보존 (각 dim 은 원래 lens 만큼 정보).
theorem pair_marginal_left {α β : Type} (L : Lens α) (M : Lens β)
    (x : Raw) : ((L.pair M).view x).1 = L.view x := by
  simp [pair_view]

theorem pair_marginal_right {α β : Type} (L : Lens α) (M : Lens β)
    (x : Raw) : ((L.pair M).view x).2 = M.view x := by
  simp [pair_view]

-- Joint image 가 product 공간 ⊆.
-- |joint| ≤ |L image| × |M image|. 많은 경우 ≪ product.
-- 대부분의 product 좌표가 **빈 칸** (no Raw maps there).
-- → sparse.
