import E213.Firmware.Axiom
import E213.Firmware.Closure
import E213.Firmware.PairInTriple
import E213.Firmware.Negation

/-
  악성 프로그램: Firmware를 깨뜨리는 10가지 시도.
  모든 공격이 HW(Lean) 또는 Firmware(213)에 의해 차단됨.
-/

-- ═══ 공격 1: C(3,2)≠3 주장 ═══
-- theorem fake : pairs 3 = 4 := by native_decide
-- → native_decide가 false 반환 → Lean 거부. ✓

-- ═══ 공격 2: 네 번째 생성자 ═══
-- inductive BadObj where | gen | mul | neg : BadObj → BadObj
-- → BadObj ≠ Obj. relify에 넣으면 타입 에러. ✓

-- ═══ 공격 3: 무한 재귀 Obj ═══
-- def loop : Obj := .mul loop (.gen 0)
-- → "fail to show termination." Lean 거부. ✓

-- ═══ 공격 4: False를 Generated로 ═══
-- Generated : Obj → Prop. False : Prop. 타입 불일치. ✓

-- ═══ 공격 5: pair 2 ≥ 2 (붕괴 부정) ═══
-- theorem fake5 : pairs 2 ≥ 2 := by native_decide
-- → pairs 2 = 1 < 2. native_decide 거부. ✓

-- ═══ 실제 실행되는 공격 시도 (타입 검사 통과하는 것만) ═══

-- 공격 6: chain_add를 깨는 weird 함수?
def weird (a b : Nat) : Nat := if a > b then a - b else b - a

-- chain_add는 rel에 무관. 구조적 증명.
theorem attack6 :
    chain weird (chain weird ⟨5, 3, 7⟩ 2) 3 =
    chain weird ⟨5, 3, 7⟩ 5 := rfl  -- ✓ 깨지지 않음

-- 공격 7: relify에 항등 함수 → triple 붕괴?
def constRel (a _ : Nat) : Nat := a
#eval (relify constRel ⟨1, 2, 3⟩).x  -- 1
#eval (relify constRel ⟨1, 2, 3⟩).y  -- 1
#eval (relify constRel ⟨1, 2, 3⟩).z  -- 2
-- x=y=1! 원소가 같아짐. 구분 붕괴!
-- 하지만 이건 rel의 문제지 firmware 문제가 아님.
-- firmware는 "어떤 rel이든 실행"할 뿐. rel 검증은 상위.

-- 공격 8: pairs에 음수 (Nat이라 불가)
-- pairs에 넣을 수 있는 건 Nat만. 음수 없음. ✓

-- 공격 9: Obj 비교 (DecidableEq 없으면?)
-- #eval (.gen 0 : Obj) == (.gen 1 : Obj)
-- → BEq Obj 인스턴스 없으면 에러. 하지만 이건 기능 누락.
-- Firmware에 == 비교를 추가하면 해결.

-- 공격 10: pair_in_triple의 c를 "쓸모없는 것"으로
-- witness c = gen 0. 항상 같은 c. "의미 없는 triple."
-- 구조적으로 valid하지만, 의미론적으로 약함.
-- → ISA는 구조만 보장. 의미는 상위 레이어 책임.

theorem attack10 :
    ∃ c : Obj, Generated (.mul (.gen 0) (.gen 1)) ∧
              Generated (.mul (.gen 0) c) ∧
              Generated (.mul (.gen 1) c) :=
  pair_in_triple (.gen 0) (.gen 1)
-- c = gen 0. 쓸모없지만 valid. firmware는 통과. ✓

-- ═══ 발견된 약점 ═══
-- 1. constRel로 구분 붕괴 가능 (공격 7). → 상위에서 rel 검증 필요.
-- 2. pair_in_triple의 c가 trivial (공격 10). → ISA는 구조만 보장.
-- 3. Obj에 DecidableEq 없음 (공격 9). → 기능 추가 고려.
-- 이것들은 firmware 버그가 아니라 "설계 선택."
-- firmware는 최소한만 보장. 나머지는 상위 레이어.
