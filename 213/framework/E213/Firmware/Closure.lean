import E213.Firmware.Axiom

/-
  폐포 정리: 모든 213 객체는 2방향으로 생성됨.

  방향 1 (gen): 원소 선택 {x, y, z}.
  방향 2 (mul): 이항 비교 ×.
  교차 혼합, 층간 비교, 임의 섞기 — 모두 ×.
  → 모두 방향 1+2로 구성. 증명: 구조 귀납.
-/

-- ═══ 213 객체의 우주: 자유 마그마 ═══

inductive Obj where
  | gen : Fin 3 → Obj       -- 방향 1: 원소 선택
  | mul : Obj → Obj → Obj   -- 방향 2: 비교 (×)

-- 이것이 전부. × 외에 객체를 만드는 방법 없음.

-- ═══ "2방향으로 생성됨" ═══

inductive Generated : Obj → Prop where
  | base : (i : Fin 3) → Generated (.gen i)
  | step : Generated a → Generated b → Generated (.mul a b)

-- ═══ 핵심 정리: 모든 객체는 Generated ═══

theorem all_generated : ∀ o : Obj, Generated o
  | .gen i => .base i
  | .mul a b => .step (all_generated a) (all_generated b)

-- 증명 끝. 구조 귀납. Obj의 생성자가 gen과 mul뿐이므로.

-- ═══ 교차 혼합 예시: 여전히 Generated ═══

-- level 0의 x와 level 1의 (x×y)를 비교:
def cross01 : Obj := .mul (.gen 0) (.mul (.gen 0) (.gen 1))

theorem cross01_ok : Generated cross01 :=
  .step (.base 0) (.step (.base 0) (.base 1))

-- level 1과 level 2의 교차:
def cross12 : Obj :=
  .mul (.mul (.gen 0) (.gen 1))
       (.mul (.mul (.gen 0) (.gen 1)) (.mul (.gen 0) (.gen 2)))

theorem cross12_ok : Generated cross12 :=
  .step (.step (.base 0) (.base 1))
        (.step (.step (.base 0) (.base 1)) (.step (.base 0) (.base 2)))

-- 아무리 복잡해도 Generated. × 를 쓰는 한.

-- ═══ 2방향의 내용 ═══

def Obj.depth : Obj → Nat
  | .gen _ => 0
  | .mul a b => 1 + max a.depth b.depth

def Obj.leaves : Obj → Nat
  | .gen _ => 1
  | .mul a b => a.leaves + b.leaves

-- depth = 방향 2(×)를 몇 번 썼는가.
-- leaves = 방향 1(gen)을 몇 번 골랐는가.
-- 모든 Obj는 (tree shape × leaf labels)로 유일하게 결정.

-- ═══ 유한 모델 𝔽₃: 교차가 새 원소를 안 만듦 ═══

def f3Closed : Bool :=
  (List.range 3).all fun a => (List.range 3).all fun b =>
    (a + b) % 3 < 3

theorem f3_stays_closed : f3Closed = true := by native_decide

-- ═══ 왜 세 번째 방향이 없는가 ═══
-- Obj에 세 번째 생성자가 없기 때문.
-- gen (방향 1) + mul (방향 2) = 전부.
-- "교차 혼합"은 mul의 입력을 다양하게 고르는 것일 뿐.
-- 새 생성자(새 방향)가 아님.
-- 세 번째 방향 = Obj에 없는 세 번째 생성자 = 존재하지 않음.
