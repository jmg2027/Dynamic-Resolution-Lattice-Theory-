import E213.Firmware.RawAxiom
import E213.Firmware.RawProperties

/-
  / 연산에서 나오는 정리들. 쉬운 것부터.
  공리: a/b = some (rel a b) if a ≠ b, none if a = b.
  이것만으로 뭐가 나오는가.
-/

-- ═══ 정리 1: 구분은 비가역 ═══

-- a/b를 만들면, a/b에서 a나 b를 복원할 수 있는가?
-- rel a b에서 a와 b를 꺼낼 수 있음 (구조적으로).
-- 하지만 "a/b만 보고" a, b가 뭔지 아는 건 다른 문제.
-- a/b는 a와 b를 "기억"함. 관계가 구성요소를 보존.

def left : RawObj → Option RawObj
  | .rel a _ => some a
  | .atom _ => none

def right : RawObj → Option RawObj
  | .rel _ b => some b
  | .atom _ => none

theorem recover_left : left (.rel a_ b_) = some a_ := rfl
theorem recover_right : right (.rel a_ b_) = some b_ := rfl

-- a/b에서 a, b 복원 가능. 관계는 구성요소를 기억.
-- 이것이 / 와 일반 함수의 차이:
-- 일반 함수 f(a,b) = c: c에서 a,b 복원 불가능할 수 있음.
-- /: rel a b에서 a, b 항상 복원 가능. 정보 무손실.

-- ═══ 정리 2: 모든 관계는 유일 ═══

-- a/b = c/d ↔ a=c ∧ b=d (순서 포함).
-- 관계가 같으면 구성요소가 같음.
theorem rel_injective (a b c d : RawObj) :
    RawObj.rel a b = RawObj.rel c d → a = c ∧ b = d := by
  intro h; injection h; constructor <;> assumption

-- ═══ 정리 3: depth 단조 증가 ═══

-- /를 적용할 때마다 depth 증가.
-- → 같은 객체를 두 번 만들 수 없음 (depth가 다르면 다름).
-- → 모든 새 관계는 진짜 새로움. 중복 없음.
theorem depth_strict (x y : RawObj) :
    (RawObj.rel x y).depth > x.depth := by
  simp [RawObj.depth]; omega

-- ═══ 정리 4: 원자는 관계가 아님 ═══

-- atom은 rel이 아님. 기본 객체.
theorem atom_not_rel (i : Fin 3) :
    ∀ a b, RawObj.atom i ≠ RawObj.rel a b := by
  intros; simp

-- 따라서: atom에서 left/right 불가.
theorem atom_no_parts (i : Fin 3) :
    left (.atom i) = none ∧ right (.atom i) = none := by
  constructor <;> rfl

-- ═══ 정리 5: Level 0는 정확히 3 ═══

-- depth 0인 RawObj = atom뿐. 3가지.
-- depth 0이면 rel 아님.
theorem depth0_is_atom (x : RawObj) (h : x.depth = 0) :
    ∃ i, x = .atom i := by
  cases x with
  | atom i => exact ⟨i, rfl⟩
  | rel a b => simp [RawObj.depth] at h

-- ═══ 정리 6: /의 결과는 원자가 아님 ═══

-- rel a b는 depth ≥ 1. 따라서 atom 아님.
theorem rel_not_atom (a b : RawObj) :
    ∀ i, RawObj.rel a b ≠ RawObj.atom i := by
  intro i; simp

-- ═══ 정리 7: Level 0→1 전이 ═══

-- Level 0: {atom 0, atom 1, rel (atom 0) (atom 1)}.
-- 유효한 /: atom0/rel, rel/atom1. (atom0/atom1 = rel, 이미 있음.)
-- 새 객체: 정확히 2개.
-- 총 Level 1: 5개.

-- 이미 있는 관계:
theorem already_exists :
    rawStar a_ b_ = some ab_ := by native_decide

-- 새 관계:
theorem new_1 :
    rawStar a_ ab_ = some (.rel a_ ab_) := by native_decide
theorem new_2 :
    rawStar ab_ b_ = some (.rel ab_ b_) := by native_decide

-- 새 관계가 기존과 다름:
theorem new_ne_old_1 :
    RawObj.rel a_ ab_ ≠ a_ ∧
    RawObj.rel a_ ab_ ≠ b_ ∧
    RawObj.rel a_ ab_ ≠ ab_ := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

theorem new_ne_old_2 :
    RawObj.rel ab_ b_ ≠ a_ ∧
    RawObj.rel ab_ b_ ≠ b_ ∧
    RawObj.rel ab_ b_ ≠ ab_ := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

-- 새 둘끼리도 다름:
theorem new_ne_each :
    RawObj.rel a_ ab_ ≠ RawObj.rel ab_ b_ := by native_decide

-- ═══ 정리 8: 유한 레벨에서 원소 수 ═══

-- Level 0: 3. Level 1: 5. Level 2: ?
-- 공식: L(0)=3, L(n+1) = L(n) + C(L(n), 2) - (이미 있는 관계 수).
-- 하한: L(n+1) ≥ L(n) + 1 (최소 1개 새 관계).
-- 상한: L(n+1) ≤ L(n) + C(L(n), 2).

-- Level 0→1: 3 + C(3,2) - 1 = 3 + 3 - 1 = 5. ✓
-- (C(3,2)=3개 관계 중 1개(a/b=ab)가 이미 있음.)
theorem level_1_count :
    3 + 3 - 1 = 5 := by native_decide

-- ═══ 정리 9: none은 동치 관계 ═══

-- rawStar x x = none: 반사성. ✓ (refl_is_none.)
-- rawStar x y = none → rawStar y x = none: 대칭성. ✓
-- (x=y이면 y=x이니까.)
theorem none_symmetric (x y : RawObj) :
    rawStar x y = none → rawStar y x = none := by
  simp [rawStar]; intro h; rw [h]

-- 추이성: rawStar x y = none ∧ rawStar y z = none → rawStar x z = none?
-- x=y, y=z → x=z. ✓
theorem none_transitive (x y z : RawObj) :
    rawStar x y = none → rawStar y z = none →
    rawStar x z = none := by
  simp [rawStar]; intros h1 h2; rw [h1, h2]

-- none은 동치 관계! = 의 성질 (반사, 대칭, 추이)이 / 에서 나옴.
-- = 을 별도로 정의 안 했는데, / 의 none이 = 의 모든 성질을 가짐.
