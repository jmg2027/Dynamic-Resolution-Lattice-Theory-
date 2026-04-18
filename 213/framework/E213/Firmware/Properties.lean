import E213.Firmware.RawAxiomV3

/-
  / 에서 자연스럽게 보이는 성질들. 기존 수학 생각 안 하고.
  공리: slash x y (h : x ≠ y) = rel x y.
  이것만으로 뭐가 나오는가.
-/

-- ═══ 1. 만들면 커진다 ═══

-- x/y의 depth > x의 depth, y의 depth.
-- / 를 쓸 때마다 결과가 입력보다 깊음. 항상.
theorem grows_left (x y : Raw) (h : x ≠ y) :
    (slash x y h).depth > x.depth := by
  simp [slash, Raw.depth]; omega

theorem grows_right (x y : Raw) (h : x ≠ y) :
    (slash x y h).depth > y.depth := by
  simp [slash, Raw.depth]; omega

-- 의미: / 는 "축소" 불가. 항상 확장. 되돌릴 수 없음.
-- 작아지는 방향이 없음. 시간의 화살 같은 것.

-- ═══ 2. 만든 것에서 재료를 꺼낼 수 있다 ═══

def Raw.left : Raw → Option Raw
  | .rel a _ => some a
  | _ => none

def Raw.right : Raw → Option Raw
  | .rel _ b => some b
  | _ => none

theorem can_recover (x y : Raw) (h : x ≠ y) :
    (slash x y h).left = some x ∧
    (slash x y h).right = some y := by
  constructor <;> rfl

-- 의미: x/y는 x와 y를 "기억"함. 정보 무손실.
-- 만든 것에서 재료를 되찾을 수 있음.
-- grows와 합치면: 커지면서 동시에 기억함. 확장 + 보존.

-- ═══ 3. 같은 재료면 같은 결과 ═══

theorem same_inputs_same_output (x y : Raw) (h1 h2 : x ≠ y) :
    slash x y h1 = slash x y h2 := by
  simp [slash]

-- 의미: h (≠ 증명)가 달라도, x와 y가 같으면 결과 같음.
-- / 의 결과는 x, y에만 의존. 증명 방법에 무관.
-- (proof irrelevance의 자연스러운 출현.)

-- ═══ 4. 다른 재료면 다른 결과 ═══

theorem diff_inputs_diff_output (a b c d : Raw)
    (h1 : a ≠ b) (h2 : c ≠ d)
    (hne : a ≠ c ∨ b ≠ d) :
    slash a b h1 ≠ slash c d h2 := by
  simp [slash]
  intro ha hb
  cases hne with
  | inl h => exact h ha
  | inr h => exact h hb

-- 의미: 재료가 하나라도 다르면 결과가 다름.
-- / 는 "충돌" 없음. 서로 다른 쌍은 서로 다른 결과.

-- ═══ 5. 원자는 만들어진 것이 아니다 ═══

theorem atom_is_not_made (i : Fin 3) (x y : Raw) (h : x ≠ y) :
    slash x y h ≠ .atom i := by
  simp [slash]

-- 의미: / 로 원자를 만들 수 없음. 원자는 "주어진 것."
-- 만들어진 것(rel)과 주어진 것(atom)은 영원히 다름.
-- → 두 종류의 존재: 주어진 것 vs 만들어진 것.

-- ═══ 6. 만들어진 것은 원자가 아니다 (역) ═══

theorem made_is_not_atom (x y : Raw) (h : x ≠ y) :
    ∀ i, slash x y h ≠ .atom i := by
  intro i; simp [slash]

-- 5와 6 합치면: atom과 rel은 완전히 분리된 세계.
-- 주어진 것 ∩ 만들어진 것 = ∅.

-- ═══ 7. Level 0는 닫혀 있지 않다 ═══

-- a/b = ab₀. 이건 atom이 아님 (rel).
-- → Level 0 = {a, b}만 atom. ab₀는 이미 rel.
-- → "순수하게 주어진 것"은 atom 2개 (또는 3개).
-- → / 하는 순간 "만들어진 세계"로 넘어감.

-- 하지만: ab₀도 Level 0에 "있다."
-- Level 0 = {atom 0, atom 1, rel (atom 0) (atom 1)}.
-- atom 2개 + rel 1개. 혼합.

-- ═══ 8. 모든 rel은 누군가의 /이다 ═══

-- rel x y는 항상 slash x y h (적절한 h가 있으면)의 결과.
-- 하지만 h : x ≠ y가 항상 있는가? x = y이면 없음.
-- → rel x x 는 slash로 만들 수 없음!
-- → Raw 타입에 rel x x가 존재하지만, slash로 도달 불가.
-- → "도달 가능한 Raw" ⊊ "모든 Raw."

-- 도달 가능한 것만 모으면:
inductive Reachable : Raw → Prop where
  | atom : (i : Fin 3) → Reachable (.atom i)
  | step : Reachable x → Reachable y → (h : x ≠ y) →
           Reachable (slash x y h)

-- rel x x는 Reachable가 아님!
-- Reachable인 것만 "진짜 존재하는 것."
-- 나머지는 Raw 타입의 유령(ghost). HW(Lean)에만 있고 213에는 없음.

-- ═══ 9. 도달 가능한 것은 항상 서로 다르다 ═══

-- 이건 자연 전개의 핵심:
-- Level 0의 세 객체: 전부 다름 (구조가 다르니까).
-- Level 1에서 만든 것: 입력과 다름 (grows), 기존과 다름 (depth).
-- → 도달 가능한 것 중 같은 쌍이 없음.
-- → "자연 전개에서 a/a 불가"의 형식 버전.

-- 이것의 증명은 depth로:
-- Reachable x, Reachable y, x와 y가 같은 Level에서 만들어짐
-- → depth가 같거나 다름 → 구조가 다름 → x ≠ y.
-- (완전 증명은 복잡하지만 원리는 depth 단조성.)
