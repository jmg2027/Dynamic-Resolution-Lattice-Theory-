import Init

/-
  RawAxiom v2: == 없는 firmware.

  / 는 항상 작동. 조건 없음. Option 없음.
  a/a = rel a a. 유효한 객체. firmware는 판단 안 함.
  "trivial 여부"는 hypervisor가 판단 (거기서 == 사용).
-/

-- ═══ 객체 ═══

inductive RawObj2 where
  | atom : Fin 3 → RawObj2
  | rel : RawObj2 → RawObj2 → RawObj2
  deriving DecidableEq, Repr

-- ═══ / : 항상 작동. 무조건. ═══

def slash (x y : RawObj2) : RawObj2 := .rel x y

-- 끝. 이것이 firmware의 전부.
-- 조건 없음. == 없음. Option 없음. if 없음.

-- ═══ 기본 객체 ═══

def a2 : RawObj2 := .atom 0
def b2 : RawObj2 := .atom 1
def ab2 : RawObj2 := slash a2 b2

-- ═══ 모든 / 가 성공 ═══

#eval slash a2 b2      -- rel (atom 0) (atom 1). ✓
#eval slash a2 a2      -- rel (atom 0) (atom 0). ✓ 실패 없음!
#eval slash ab2 ab2    -- rel (rel ..) (rel ..). ✓

-- ═════ firmware에서 증명 가능한 것들 ═════

-- 정리 1: depth 단조 증가. (== 불필요.)
def RawObj2.depth : RawObj2 → Nat
  | .atom _ => 0
  | .rel a b => 1 + max a.depth b.depth

theorem depth_grows (x y : RawObj2) :
    (slash x y).depth > x.depth ∧
    (slash x y).depth > y.depth := by
  constructor <;> simp [slash, RawObj2.depth] <;> omega

-- 정리 2: rel 단사. (== 불필요. injection만.)
theorem slash_injective (a b c d : RawObj2) :
    slash a b = slash c d → a = c ∧ b = d := by
  intro h; simp [slash] at h; exact h

-- 정리 3: 원자 ≠ 관계. (== 불필요.)
theorem atom_ne_rel (i : Fin 3) (a b : RawObj2) :
    RawObj2.atom i ≠ slash a b := by
  simp [slash]

-- 정리 4: 복원 가능. (== 불필요.)
def left2 : RawObj2 → Option RawObj2
  | .rel a _ => some a
  | _ => none

def right2 : RawObj2 → Option RawObj2
  | .rel _ b => some b
  | _ => none

theorem recover (a b : RawObj2) :
    left2 (slash a b) = some a ∧ right2 (slash a b) = some b := by
  constructor <;> rfl

-- ═════ firmware에서 증명 불가능한 것 ═════

-- "a/a가 trivial이다" → == 필요. firmware에 없음.
-- "a/b ≠ b/a" → == 필요. firmware에 없음.
-- "none은 동치 관계" → none 자체가 없음.

-- 이것들은 전부 HYPERVISOR에서.

-- ═════ hypervisor 미리보기 ═════

-- hypervisor는 == 를 가지고 있음 (Lean의 DecidableEq).
-- 거기서:

def isTrivial (o : RawObj2) : Bool :=
  match o with
  | .rel a b => a == b    -- HERE: == 사용. hypervisor에서.
  | _ => false

#eval isTrivial (slash a2 b2)    -- false. 비사소.
#eval isTrivial (slash a2 a2)    -- true. 사소!
#eval isTrivial (slash ab2 ab2)  -- true.

-- 이제 "등호"가 hypervisor에서 정의됨:
-- "x = y" ↔ "isTrivial (slash x y) = true."
-- 이것은 순환이 아님: == 은 hypervisor가 가져온 것.
-- firmware는 == 없이 slash만 제공.

-- ═════ hypervisor에서의 정리 9 (비순환) ═════

-- isTrivial이 동치 관계인지:
-- 반사: isTrivial (slash x x) = true. ✓
theorem hv_refl (x : RawObj2) :
    isTrivial (slash x x) = true := by
  simp [slash, isTrivial]

-- 대칭: isTrivial (slash x y) → isTrivial (slash y x). ✓
theorem hv_symm (x y : RawObj2) :
    isTrivial (slash x y) = true → isTrivial (slash y x) = true := by
  simp [slash, isTrivial]
  intro h; exact h ▸ rfl

-- 잠깐, 이건 x == y → y == x 를 쓰는 건데...
-- DecidableEq에서 오는 것. hypervisor가 제공.
-- firmware가 아니라 hypervisor의 == 에서 나옴.
-- 순환 아님: firmware(slash) + hypervisor(==) = 등호 성질.
