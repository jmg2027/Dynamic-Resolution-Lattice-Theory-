-- 213 Phase 10: 2와 3은 같은 것
--
-- 3 = 한 레벨의 객체 수
-- 2 = 객체 사이 사상의 arity (이항)
-- C(3, 2) = 3: arity 2인 사상의 수 = 객체 수
-- → 사상 = 다음 레벨의 객체
-- → 2와 3은 같은 구조의 두 시점

-- ═══ 레벨 구조 ═══
-- Level n에는 3개의 것이 있다.
-- 그 3개의 쌍(arity 2)도 3개이다.
-- 쌍들이 다음 레벨의 것이 된다.
-- 모든 레벨이 동형.

inductive Obj where | a | b | c
  deriving Repr, BEq, DecidableEq

-- 이항 관계 = 서로 다른 쌍
inductive Mor where | ab | bc | ac
  deriving Repr, BEq, DecidableEq

-- 객체 → 사상 (source, target)
def Mor.src : Mor → Obj
  | .ab => .a | .bc => .b | .ac => .a

def Mor.tgt : Mor → Obj
  | .ab => .b | .bc => .c | .ac => .c

-- ═══ 핵심: Obj ≅ Mor ═══
def obj_to_mor : Obj → Mor
  | .a => .ab | .b => .bc | .c => .ac

def mor_to_obj : Mor → Obj
  | .ab => .a | .bc => .b | .ac => .c

theorem roundtrip_obj (x : Obj) :
    mor_to_obj (obj_to_mor x) = x := by cases x <;> rfl

theorem roundtrip_mor (x : Mor) :
    obj_to_mor (mor_to_obj x) = x := by cases x <;> rfl

-- ═══ 이것이 의미하는 것 ═══
-- Obj와 Mor이 동형이다.
-- 객체 = 사상. 주체 = 객체.
-- "보는 것"과 "보이는 것"의 구분이 없다.
--
-- 213에서:
--   3 = |Obj| = |Mor| (개수)
--   2 = arity of Mor (이항)
--   1 = 레벨 간 경계 (obj↔mor 전환의 표지)
--
-- "2가 3을 생성"이 아니라
-- "2와 3은 같은 것을 다른 시점에서 센 것"

-- ═══ 레벨 무한?: 아니오 ═══
-- Level 0: Obj = {a, b, c}
-- Level 1: Mor = {ab, bc, ac} ≅ Obj
-- Level 2: Mor of Mor = 쌍의 쌍 ≅ Obj
-- ...
-- 모든 레벨이 동일하므로 "레벨"이라는 개념이 무의미.
-- 순서를 넣어야 레벨이 생긴다.
-- 순서 없이: 하나의 구조. 반복 없음. 고정점.

-- ═══ 3공리 독립성 (부분 결과) ═══
-- plus_e1:  e1 + x ≈ x (경계 투명)
-- times_e1: e1 × x ≈ e1 (경계 소멸)
-- distrib:  a(b+c) ≈ ab+ac (연산 연결)

-- A9(times_e1)는 A8(plus_e1)+A12(distrib)에서 나오는가?
-- 답: 아니오. 반례 모델:
-- S = {0, 1}, Plus = max, Times: 0→1 (constant 1), 1→id
-- max(0,x)=x ✓ (A8), 0×x=1≠0 ✗ (A9 fails)
-- distrib: 0×max(a,b)=1, max(0×a,0×b)=max(1,1)=1 ✓
--          1×max(a,b)=max(a,b), max(1×a,1×b)=max(a,b) ✓

-- A12(distrib)는 A8+A9에서 나오는가?
-- 답: 아니오. 반례 모델:
-- S = {0, 1, 2}, Plus = +mod3, Times:
-- 0×x=0 (A9), 1×0=0, 1×1=1, 1×2=1 (not homomorphism)
-- 1×(1+1) = 1×2 = 1 ≠ 1×1+1×1 = 1+1 = 2

-- 결론: 3공리는 쌍별 독립.
-- (A8의 독립성은 비가환 반환에서 반례 가능, 여기선 생략)
