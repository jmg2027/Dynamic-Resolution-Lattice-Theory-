import E213.Firmware.RawAxiom

/-
  rawStar의 성질 탐구.
  * 만 있고 = 은 부재인 체계에서 뭐가 나오는가.
-/

-- ═══ 기본 성질 ═══

-- 성질 1: 반사성 = none.
-- ∀ x, rawStar x x = none.
theorem refl_is_none (x : RawObj) : rawStar x x = none := by
  simp [rawStar]

-- 성질 2: x ≠ y이면 rawStar는 some.
theorem neq_gives_some (x y : RawObj) (h : x ≠ y) :
    (rawStar x y).isSome = true := by
  simp [rawStar, h]

-- 성질 3: 교환법칙?
-- rawStar x y = rawStar y x ? 결과가 rel x y vs rel y x. 다름!
-- 교환 아님! rel x y ≠ rel y x (구조가 다름).
theorem not_commutative :
    rawStar a_ b_ ≠ rawStar b_ a_ := by native_decide

-- 하지만 둘 다 some (둘 다 성공):
theorem both_some :
    (rawStar a_ b_).isSome = true ∧
    (rawStar b_ a_).isSome = true := by
  constructor <;> native_decide

-- "성공 여부"는 대칭. "결과값"은 비대칭.
-- 성공/실패만 보면 교환. 내용까지 보면 비교환.
-- → 교환법칙이 "어느 수준에서" 성립하는가가 중요.

-- ═══ 결과의 구조 ═══

-- 성질 4: 결과는 항상 rel.
-- rawStar x y = some z → z = rel x y.
theorem result_is_rel (x y : RawObj) (h : x ≠ y) :
    rawStar x y = some (.rel x y) := by
  simp [rawStar, h]

-- 성질 5: 결과는 입력과 다름.
-- rel x y ≠ x ∧ rel x y ≠ y.
-- 이건 일반적으로 참? RawObj에서 rel x y는 구조적으로 x, y와 다름.
-- rel x y의 depth > max(x.depth, y.depth)이면 자명.

def RawObj.depth : RawObj → Nat
  | .atom _ => 0
  | .rel a b => 1 + max a.depth b.depth

-- 결과의 depth > 입력의 depth.
theorem result_deeper (x y : RawObj) :
    (RawObj.rel x y).depth > x.depth ∧
    (RawObj.rel x y).depth > y.depth := by
  constructor <;> simp [RawObj.depth] <;> omega

-- 따라서 결과 ≠ 입력. (depth가 다르면 다름.)
-- → * 는 항상 "새 것"을 만듦. 기존 것을 재활용 안 함.

-- ═══ Level별 객체 수 ═══

-- Level 0: {a, b, ab}. 3개.
-- 유효한 * : a*b, a*ab, b*a, b*ab, ab*a, ab*b. 하지만:
-- a*b = rel a b, b*a = rel b a. 둘 다 유효. 서로 다름!
-- 교환 안 하면: 6개의 유효한 *. (3개 × 2개 = C(3,2)×2 = 6.)
-- 교환 하면: 3개. (비순서쌍.)

-- 비교환 세계:
-- Level 0: 3개. 새 관계: 6개. 총 9개.
-- Level 1: 9개. 새 관계: 9×8 = 72개. 총 81개.
-- Level n: 3^(2^n)?? 급격 성장.

-- 교환 세계:
-- Level 0: 3개. 새 관계: C(3,2) = 3개. 총 6개.
-- Level 1: 6개. 새 관계: C(6,2) = 15개. 총 21개.
-- 여전히 급성장.

-- ═══ 폐포 크기 ═══

-- depth d까지의 RawObj 수:
-- depth 0: 3 (atom 3개).
-- depth 1: 3 + 6 = 9 (비교환). 또는 3 + 3 = 6 (교환, 중복 제거).
-- 교환일 때: depth 1에서 {rel a b, rel a ab, rel b ab} (ab = rel a b).

-- 구체 계산 (depth 1):
#eval rawStar a_ b_    -- rel a b
#eval rawStar a_ ab_   -- rel a (rel a b)
#eval rawStar b_ ab_   -- rel b (rel a b)
#eval rawStar b_ a_    -- rel b a        ← 교환이면 rel a b와 같음
#eval rawStar ab_ a_   -- rel (rel a b) a ← 교환이면 rel a (rel a b)와 같음
#eval rawStar ab_ b_   -- rel (rel a b) b

-- 비교환: 6개 결과 전부 다름.
-- 교환: 3개 (중복 제거).

-- ═══ none의 분포 ═══

-- 전체 3×3 = 9 쌍 중:
-- none: 3개 (a*a, b*b, ab*ab). 대각선.
-- some: 6개 (비대각선).
-- none 비율 = 3/9 = 1/3. 항상 1/n (n개 객체에서).

-- Level 1 (9개 객체): none = 9/81 = 1/9.
-- Level n (k개 객체): none = k/k² = 1/k.
-- → none 비율이 0으로 감소! = 이 점점 드물어짐.
-- 큰 세계에서: 거의 모든 쌍이 ≠. = 은 희귀.

-- 이것이 "= 은 부재"의 정량적 의미:
-- 세계가 커질수록 = 은 비율 → 0.
-- = 은 "일반적"이지 않고 "특수한" 상태.

-- ═══ rawStar의 결합법칙? ═══

-- (a*b)*c vs a*(b*c). 둘 다 some (a≠b≠c이면).
-- (a*b)*c = rel (rel a b) c.
-- a*(b*c) = rel a (rel b c).
-- 이 둘은 다름! (트리 구조가 다름.)
-- → 결합법칙 불성립. rawStar는 비결합적.

theorem not_associative :
    rawStar (RawObj.rel a_ b_) (.atom 2) ≠
    rawStar a_ (RawObj.rel b_ (.atom 2)) := by
  native_decide

-- 비교환 + 비결합 = 자유 마그마. 가장 약한 대수 구조.
-- 교환/결합 법칙은 QUOTIENT로 추가됨 (상위 레이어).

-- ═══ rawStar의 유일한 법칙 ═══

-- 법칙 1: x*x = none. (반사 = 부재.)
-- 법칙 2: x≠y → x*y = some (rel x y). (비반사 = 새 것.)
-- 법칙 3: depth(x*y) > depth(x), depth(y). (결과 > 입력.)

-- 이 셋이 전부. 교환도 결합도 없음.
-- 이것이 213의 가장 날것의 형태:
-- "다른 둘을 비교하면 새 것이 나오고, 같은 것은 비교 불가."

-- ═══ 요약 ═══

structure RawProperties where
  refl_none : ∀ x : RawObj, rawStar x x = none
  neq_some : ∀ x y : RawObj, x ≠ y → (rawStar x y).isSome = true
  result_new : ∀ x y : RawObj,
    (RawObj.rel x y).depth > x.depth ∧
    (RawObj.rel x y).depth > y.depth
  not_comm : rawStar a_ b_ ≠ rawStar b_ a_
  not_assoc : rawStar (RawObj.rel a_ b_) (.atom 2) ≠
              rawStar a_ (RawObj.rel b_ (.atom 2))

theorem raw_props : RawProperties where
  refl_none := refl_is_none
  neq_some := neq_gives_some
  result_new := result_deeper
  not_comm := by native_decide
  not_assoc := by native_decide
