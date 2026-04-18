import E213.Firmware.Axiom
import E213.Firmware.Closure
import E213.Translation.Translate

/-
  sorry의 아키텍처적 의미.
  sorry = 검증 스택의 구멍. 어디에 있느냐가 의미를 결정.
-/

-- ═══ Layer 0 (HW): sorry 불가 ═══
-- Lean 커널 자체에 sorry 없음. 커널은 완전.
-- sorry는 커널이 "여기 구멍 있음"이라고 표시하는 것.
-- HW 멀펑션 아님. HW가 정직하게 "미검증" 보고.

-- ═══ Layer 1 (FW): sorry = ISA 미완성 ═══
-- 213의 규칙이 증명 아닌 가정이면 sorry.
-- 예: "theorem fake : pairs 3 = 3 := sorry"
-- → ISA 규칙을 HW로 검증 안 함. 회로 없는 명령어.
-- 현재: 0 sorry. 모든 ISA 규칙이 HW 검증됨. ✓

-- 실제로 sorry가 필요한 FW 규칙이 있는가?
-- pairs 3 = 3: native_decide. ✓
-- all_generated: 구조 귀납. ✓
-- chain_add: 귀납. ✓
-- → FW에 sorry 필요 없음. ISA가 완전.

-- ═══ Layer 1↔2 (번역): sorry = 번역 미완성 ═══
-- 213 ↔ 수학의 대응이 증명 안 되면 sorry.
-- 예: "chain이 ℕ의 모든 성질을 보존"은 부분만 증명.
-- chain_add (덧셈): ✓
-- chain_mul (곱셈): 미구현. sorry 필요할 것.
-- → 번역이 불완전. 하지만 번역 자체가 불가능한 건 아님.

-- ═══ Layer 2 (HV): sorry = 공리체계 미구현 ═══
-- PA를 213 위에 올렸는데, PA의 일부 공리가 검증 안 되면 sorry.
-- 예: PA 귀납 공리 = Lean의 Nat.rec 사용. 213에서 자체 도출?
-- 현재: Lean HW에 의존. 213 자체 도출 = 미완.

-- ═══ Layer 3 (OS): sorry = 증명 안 됨 ═══
-- 정리가 참이지만 증명을 못 찾음.
-- 예: theorem goldbach_all : ∀ n, ... := sorry
-- → 두 가지 가능성:
--   (a) 증명 가능하지만 아직 못 찾음. (탐색 문제.)
--   (b) 이 레이어의 API로 증명 불가. (표현력 한계.)

-- ═══ sorry의 3가지 종류 ═══

-- 종류 1: "아직 못 찾음" (depth ≤ 2).
-- 대수적 정리. 유한 검사로 해결 가능. 시간 문제.
-- 예: 유한 군의 성질.
-- sorry 해소: native_decide 또는 유한 귀납.

-- 종류 2: "이 레이어로는 부족" (depth ω).
-- ∀n 문제. 유한 API로 무한 주장. 레이어 초과.
-- 예: Goldbach ∀n.
-- sorry 해소: 상위 레이어 추가 또는 ISA 확장.

-- 종류 3: "원리적으로 불가" (depth > ε₀).
-- PA 독립. 괴델 문장. sorry 해소: 불가. 새 공리 필요.

-- ═══ 당신의 직관 검증 ═══
-- "sorry 필요 = 213으로 표현 안 됨?"
-- 부분적으로 맞음. 정확히는:

-- sorry in FW = 213 ISA 자체가 미완성.     (현재 없음.)
-- sorry in 번역 = 213↔수학 대응 미완성.    (부분적.)
-- sorry in HV = 공리체계 미구현.            (부분적.)
-- sorry in OS = 증명 미발견 또는 표현력 부족. (핵심.)

-- "213으로 표현 안 됨" = sorry 종류 2 또는 3.
-- "213으로 표현은 되지만 증명 못 찾음" = sorry 종류 1.
-- 구분 기준: depth.
-- depth ≤ 2: 종류 1. 찾으면 됨.
-- depth ω: 종류 2. 레이어 확장 필요.
-- depth > ε₀: 종류 3. 원리적 한계.

-- ═══ Goldbach의 sorry ═══
-- 개별 goldbach(n): depth 1. 종류 1. native_decide.
-- ∀n: depth ω. 종류 2. FW만으론 부족. HV에 새 API 필요.
-- 그 새 API = "213 원리" (¬만으로 정의+열거불가 → ∅).
