import E213.OS.Provability

/-
  OS Layer: Topology 를 / 위에.

  3점 공간 (Fin 3) 의 위상.
  열린집합 = 부분집합 (Fin 3 → Bool).
  위상 = 열린집합의 list.

  213 해석:
    위상 T = "T-구별 가능성" 을 판정하는 렌즈 가족.
    두 점 x, y 는 T-구별 불가 (topIndist)
      ⟺ 모든 열린집합에서 같은 값
      ⟺ T 의 kernel 에 속함.

  위상동형 = 두 위상이 Fin 3 의 permutation 아래 같은 kernel.
  즉 "위상 = 특정 kernel 구조" 의 명시 형태.
-/

-- 열린집합: Fin 3 → Bool (characteristic function).
def OpenSet : Type := Fin 3 → Bool

-- 위상: 열린집합의 list.
def Topology3 : Type := List OpenSet

-- ═══ 표준 위상 ═══

-- Discrete: 모든 부분집합 열림.
def discrete3 : Topology3 :=
  [fun _ => false,
   fun i => i.val == 0,
   fun i => i.val == 1,
   fun i => i.val == 2,
   fun i => i.val == 0 || i.val == 1,
   fun i => i.val == 0 || i.val == 2,
   fun i => i.val == 1 || i.val == 2,
   fun _ => true]

-- Trivial: {∅, 전체} 만.
def trivial3 : Topology3 :=
  [fun _ => false, fun _ => true]

-- Sierpinski: {∅, {0}, 전체}.
def sierpinski3 : Topology3 :=
  [fun _ => false, fun i => i.val == 0, fun _ => true]

-- ═══ 위상적 구별 불가능 (topological indistinguishability) ═══

-- 두 점 x, y 가 T-구별 불가: 모든 열린집합에서 같은 값.
def topIndist (T : Topology3) (x y : Fin 3) : Prop :=
  ∀ U ∈ T, U x = U y

instance (T : Topology3) (x y : Fin 3) : Decidable (topIndist T x y) :=
  List.decidableBAll _ _

-- ═══ 구체 검증 ═══

-- Discrete: 모든 점 서로 구별.
example : ¬ topIndist discrete3 0 1 := by decide
example : ¬ topIndist discrete3 1 2 := by decide

-- Trivial: 모든 점 같음.
example : topIndist trivial3 0 1 := by decide
example : topIndist trivial3 1 2 := by decide

-- Sierpinski: 0 은 구별, 1 과 2 는 구별 불가.
example : ¬ topIndist sierpinski3 0 1 := by decide
example : topIndist sierpinski3 1 2 := by decide

-- ═══ 213 해석: 위상 = 렌즈 kernel 구조 ═══

-- topIndist T 는 자동 동치관계 (open set 구별의 일반 사실).
theorem topIndist_refl (T : Topology3) (x : Fin 3) :
    topIndist T x x := fun _ _ => rfl

theorem topIndist_symm (T : Topology3) {x y : Fin 3} :
    topIndist T x y → topIndist T y x :=
  fun h U hU => (h U hU).symm

theorem topIndist_trans (T : Topology3) {x y z : Fin 3} :
    topIndist T x y → topIndist T y z → topIndist T x z :=
  fun h1 h2 U hU => (h1 U hU).trans (h2 U hU)

-- → topIndist 는 Fin 3 위의 Setoid.
def topSetoid (T : Topology3) : Setoid (Fin 3) where
  r := topIndist T
  iseqv := ⟨topIndist_refl T, topIndist_symm T, topIndist_trans T⟩

-- ═══ 위상동형: kernel 일치 (permutation 허용) ═══

-- T1 이 T2 와 위상동형 가능:
-- Fin 3 의 permutation σ 가 존재해 T1-indist ↔ T2-indist (σx, σy).
def isHomeomorphic (T1 T2 : Topology3) : Prop :=
  ∃ σ : Fin 3 → Fin 3, Function.Bijective σ ∧
    ∀ x y, topIndist T1 x y ↔ topIndist T2 (σ x) (σ y)

-- Discrete 는 자기 자신과 homeomorphic.
example : isHomeomorphic discrete3 discrete3 := by
  refine ⟨id, Function.bijective_id, ?_⟩
  intros x y; rfl

-- Sierpinski 는 "0 isolated" 버전과, "1 isolated" 버전 서로 homeomorphic.
def sierpinski3' : Topology3 :=
  [fun _ => false, fun i => i.val == 1, fun _ => true]

-- σ: 0 ↔ 1 swap.
-- 실제 증명은 permutation 교환 + topIndist 구조.
-- (생략: permutation 명시적 구성 필요.)

-- ═══ 결론 ═══

-- 위상 T = Fin 3 위의 partition (topIndist 의 동치류).
-- 213 해석: 위상 ⊆ Lens kernel 구조.
-- 위상동형 = kernel 같음 (permutation 아래).
-- 이미 LensKernel 의 일반 framework 로 표현 가능.
