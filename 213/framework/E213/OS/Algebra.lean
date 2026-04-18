import E213.OS.Provability

/-
  OS Layer: 대수 구조 (Z/3Z) 를 / 위에.

  렌즈: Lens.Z3 (α = Fin 3, g = id, h = 덧셈 mod 3).

  인코딩:
    원소       → atom i
    연산 x + y → rel x y  (Lens.view 로 Fin 3 값)

  공리: 그룹 (단위원, 역원, 결합, 교환) — 모두 decide.

  흥미 지점:
    slash 는 ≠ 제약 있어서 rel x x 거부.
    하지만 Lens.view 는 모든 Raw 에서 계산 가능 (Reachable 아닌 것도).
    → 그룹 연산은 Raw 전체에서 정의됨.
    → "Reachable 구조" 와 "대수 구조" 의 분리.
-/

-- ═══ Z/3Z 덧셈 ═══

-- Fin 3 위 mod 3 덧셈. (Lean 이 자동 제공하지만 명시.)
def Fin3.add : Fin 3 → Fin 3 → Fin 3 :=
  fun a b => ⟨(a.val + b.val) % 3, Nat.mod_lt _ (by decide)⟩

-- 그룹 공리 (decide 검증).
example : ∀ a : Fin 3, Fin3.add ⟨0, by decide⟩ a = a := by decide
example : ∀ a : Fin 3, Fin3.add a ⟨0, by decide⟩ = a := by decide
example : ∀ a b : Fin 3, Fin3.add a b = Fin3.add b a := by decide
example : ∀ a b c : Fin 3, Fin3.add (Fin3.add a b) c = Fin3.add a (Fin3.add b c) :=
  by decide

-- 역원.
def Fin3.neg : Fin 3 → Fin 3 :=
  fun a => ⟨(3 - a.val) % 3, Nat.mod_lt _ (by decide)⟩

example : ∀ a : Fin 3, Fin3.add a (Fin3.neg a) = ⟨0, by decide⟩ := by decide

-- ═══ Z/3Z 를 Lens 로: Raw → Fin 3 ═══

def Lens.Z3 : Lens (Fin 3) :=
  ⟨id, Fin3.add⟩

-- ═══ 구체 계산 ═══

-- Reachable 한 rel: atom 0 + atom 1 = 1.
example : Lens.Z3.view (Raw.rel a₀ b₀) = ⟨1, by decide⟩ := by decide

-- atom 1 + atom 2 = 0 (mod 3). 순환군의 핵심!
example : Lens.Z3.view (Raw.rel b₀ (.atom 2)) = ⟨0, by decide⟩ := by decide

-- ═══ Reachable 밖 에서도 연산 정의 ═══

-- slash 는 rel a₀ a₀ 거부. 하지만 Raw.rel a₀ a₀ 자체는 constructor 로 가능.
-- 그 위의 Lens.Z3.view 는 계산됨 (fold 가 ≠ 제약 없음).

-- 0 + 0 = 0.
example : Lens.Z3.view (Raw.rel a₀ a₀) = ⟨0, by decide⟩ := by decide

-- 1 + 1 = 2.
example : Lens.Z3.view (Raw.rel b₀ b₀) = ⟨2, by decide⟩ := by decide

-- 2 + 2 = 1 (mod 3).
example : Lens.Z3.view (Raw.rel (.atom 2) (.atom 2)) = ⟨1, by decide⟩ := by decide

-- 이 rel 들은 Reachable 이 아님:
example : ¬ Reachable (Raw.rel a₀ a₀) := by decide
example : ¬ Reachable (Raw.rel b₀ b₀) := by decide

-- → 그룹 연산은 Raw 전체 에서 정의. Reachable 제약 밖.
-- Algebra 는 Firmware 의 ≠ 제약과 독립한 구조.

-- ═══ 그룹 공리 on Raw (Lens.Z3.view 통해) ═══

-- 덧셈 결합 (Fin 3 의 결합 을 그대로 올림).
theorem z3_assoc (x y z : Raw) :
    Fin3.add (Fin3.add (Lens.Z3.view x) (Lens.Z3.view y)) (Lens.Z3.view z) =
    Fin3.add (Lens.Z3.view x) (Fin3.add (Lens.Z3.view y) (Lens.Z3.view z)) := by
  revert x y z
  decide

-- 교환 (abelian).
theorem z3_comm (x y : Raw) :
    Fin3.add (Lens.Z3.view x) (Lens.Z3.view y) =
    Fin3.add (Lens.Z3.view y) (Lens.Z3.view x) := by
  revert x y
  decide

-- ═══ 해석 ═══

-- 공리계 = 렌즈 + binary operation (group, ring, ...)
-- Algebra 는 Raw 의 "rel constructor" 를 연산 기호로 재해석.
-- ≠ 제약 은 여기서 해소됨: Lens.view 는 모든 Raw 에서 정의.

-- 다른 α 로 확장 가능:
--   Lens (Fin n) : 순환군 Z/nZ.
--   Lens (Bool)  : Z/2Z (already truthValue).
--   Lens (Int)   : Z (무한 아벨 군).

-- 이게 "대수 에서 같다" 의 / 해석:
--   x ≡_alg y ⟺ Lens.Z3.view x = Lens.Z3.view y
--              ⟺ 두 Raw 가 group 에서 같은 원소 표현.

-- Z3 kernel 예: rel a₀ a₀ (0+0=0) 과 rel b₀ (rel a₀ b₀) (1+(0+1)=2?  확인)
-- Lens.Z3.view (rel b₀ (rel a₀ b₀)) = 1 + (0+1) = 1+1 = 2. 다른 원소.
-- 그러므로 kernel 섬세함은 계산에 의존.
