import E213.Hypervisor.NumberComparison

/-
  수를 만드는 일반 규칙: fold (catamorphism).

  관찰: 지금까지 본 모든 수들이 같은 모양.
    f(atom i) = g(i)
    f(rel x y) = h(f x, f y)

  두 데이터만 고르면 수 한 개 생성:
    g : Fin 3 → α   — 각 원자의 초기값
    h : α → α → α   — 두 자식의 결합 규칙

  이것이 "수를 만드는 일반 규칙."
  α는 Nat에 한정되지 않음 (Bool, List, String 등 모두).

  결과:
    - 모든 "구조적 수"는 fold의 특수화.
    - h가 commutative이면 수는 좌우 대칭.
    - h가 비대칭이면 수는 좌우 구별.
-/

-- ═══ 일반 fold: Raw의 임의 데이터로의 catamorphism ═══

def Raw.fold {α : Type} (g : Fin 3 → α) (h : α → α → α) : Raw → α
  | .atom i  => g i
  | .rel x y => h (x.fold g h) (y.fold g h)

-- ═══ 기존 수들을 fold로 재표현 ═══

-- depth : g = 상수 0, h = (1 + max).
theorem depth_as_fold (x : Raw) :
    x.depth = x.fold (fun _ => 0) (fun a b => 1 + max a b) := by
  induction x with
  | atom _ => rfl
  | rel a b iha ihb => simp [Raw.depth, Raw.fold, iha, ihb]

-- leaves : g = 상수 1, h = 합.
theorem leaves_as_fold (x : Raw) :
    x.leaves = x.fold (fun _ => 1) (· + ·) := by
  induction x with
  | atom _ => rfl
  | rel a b iha ihb => simp [Raw.leaves, Raw.fold, iha, ihb]

-- nodes : g = 상수 1, h = (1 + 합).
theorem nodes_as_fold (x : Raw) :
    x.nodes = x.fold (fun _ => 1) (fun a b => 1 + a + b) := by
  induction x with
  | atom _ => rfl
  | rel a b iha ihb => simp [Raw.nodes, Raw.fold, iha, ihb]

-- ═══ 대칭성 조건: h commutative ⇒ fold 대칭 ═══

-- h가 대칭이면 fold는 rel의 좌우 순서를 구별 못 함.
theorem fold_comm {α : Type} (g : Fin 3 → α) (h : α → α → α)
    (hcomm : ∀ a b, h a b = h b a) (x y : Raw) :
    (Raw.rel x y).fold g h = (Raw.rel y x).fold g h := by
  simp [Raw.fold]; exact hcomm _ _

-- 따름정리: depth, leaves, nodes는 좌우 대칭 (h가 commutative).
example (x y : Raw) :
    (Raw.rel x y).depth = (Raw.rel y x).depth := by
  simp [depth_as_fold]
  exact fold_comm _ _ (fun a b => by rw [Nat.max_comm]) x y

-- ═══ 비대칭 수의 예시: leftSpine ═══

-- h가 비대칭이면 수는 좌우 구별.
-- leftSpine: 왼쪽만 따라가는 길이. h(a, _) = a + 1.
def Raw.leftSpine (x : Raw) : Nat :=
  x.fold (fun _ => 0) (fun a _ => a + 1)

def Raw.rightSpine (x : Raw) : Nat :=
  x.fold (fun _ => 0) (fun _ b => b + 1)

-- aab₀ = a / (a/b) = rel a (rel a b).
-- leftSpine (rel a (rel a b)) = leftSpine a + 1 = 0 + 1 = 1 (왼쪽은 atom).
-- rightSpine (rel a (rel a b)) = rightSpine (rel a b) + 1 = 1 + 1 = 2.
example : aab₀.leftSpine  = 1 := by decide
example : aab₀.rightSpine = 2 := by decide

-- bab₀ = b / (a/b) = rel b (rel a b). 같은 구조.
example : bab₀.leftSpine  = 1 := by decide
example : bab₀.rightSpine = 2 := by decide

-- leftSpine ≠ rightSpine (aab₀). 비대칭 수는 존재.
example : aab₀.leftSpine ≠ aab₀.rightSpine := by decide

-- 비대칭 수는 rel 좌우를 구별: aab₀ vs bab₀는 같은 spine이지만,
-- rel a (rel a b) vs rel (rel a b) a 는 다른 leftSpine/rightSpine.

-- ═══ fold의 표현력: α = Nat 말고도 ═══

-- α = Bool: 원자 판별 수. "모두 atom 0인가?"
def Raw.allAtomZero (x : Raw) : Bool :=
  x.fold (fun i => i.val == 0) (fun a b => a && b)

example : a₀.allAtomZero = true := by decide
example : b₀.allAtomZero = false := by decide
example : ab₀.allAtomZero = false := by decide

-- α = List Raw: 서브트리 리스트.
def Raw.allSubs (x : Raw) : List Raw :=
  x.fold (fun i => [.atom i]) (fun xs ys => xs ++ ys)

example : ab₀.allSubs = [a₀, b₀] := by decide
-- (leaves만 담김 — rel 자기자신 빠짐. 그건 다른 fold로.)

-- ═══ 일반 규칙 정리 ═══

-- 수 하나 만들기 = (α, g, h) 세 쌍 고르기.
--   α : 타입 (보통 Nat, 하지만 자유).
--   g : Fin 3 → α   — 원자의 초기값.
--   h : α → α → α   — rel에서의 결합.
--
-- 성질:
--   h commutative ⟺ 수가 좌우 대칭.
--   h associative → fold도 associative (자연).
--   h idempotent  → depth-like (max, min).
--   h 순수 합계   → leaves/nodes-like.
--
-- 예: 이미 정의된 수들은 모두 특수 fold.
--   depth      = fold (const 0) (1 + max)
--   leaves     = fold (const 1) (+)
--   nodes      = fold (const 1) (fun a b => 1+a+b)
--   leftSpine  = fold (const 0) (fun a _ => a+1)  비대칭
--   rightSpine = fold (const 0) (fun _ b => b+1)  비대칭
--   allAtomZero= fold (·.val == 0) (∧)  Bool
--   allSubs    = fold ([·]) (++)  List

-- 결론:
-- / 는 트리를 만든다. Raw.fold는 그 트리에서 임의의 수/값을 뽑는다.
-- 수 = (초기값 + 결합 규칙)의 선택. 무한히 많음.
-- 구조적 수는 전부 fold의 특수화.
