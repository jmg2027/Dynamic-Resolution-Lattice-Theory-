import E213.Hypervisor.Lens

/-
  Lens Kernel: "같다"의 진짜 출처.

  핵심 통찰:
    두 Raw가 같은 Lens 값을 가지면 → 그 Lens 위의 이론에서 "같다."

    =_L  :=  ker(L.view)  =  { (x, y) : L.view x = L.view y }

  동치관계의 세 성질이 공짜:
    kernel이 자동으로 동치관계 (함수의 일반 성질).
    Lean의 == 에서 빌려온 게 아님.
    정리 9의 순환이 여기서 풀림.

  다른 공리계 = 다른 Lens = 다른 "같다":
    - PA    : depth 렌즈 → 깊이가 같은 트리.
    - 논리  : Bool 렌즈 → 진리값이 같은 트리.
    - 집합론: List 렌즈 → 부분집합이 같은 트리.
    - 기하  : (depth, leaves) pair → 둘 다 같은 트리.
    - id'   : Raw 렌즈 → 자기 자신만 같은 (가장 섬세).

    거친 Lens → 많이 같음 (Bool).
    섬세한 Lens → 덜 같음 (Raw).
-/

-- ═══ Lens가 만드는 동치관계: kernel ═══

def Lens.equiv {α : Type} (L : Lens α) (x y : Raw) : Prop :=
  L.view x = L.view y

-- 표기.
notation:50 x " =[" L "] " y => Lens.equiv L x y

-- ═══ 동치관계의 세 성질 — kernel의 일반 사실 ═══

-- 반사: L.view x = L.view x. 자명.
theorem Lens.equiv_refl {α : Type} (L : Lens α) (x : Raw) :
    L.equiv x x := rfl

-- 대칭: kernel은 자동 대칭.
theorem Lens.equiv_symm {α : Type} (L : Lens α) {x y : Raw} :
    L.equiv x y → L.equiv y x := Eq.symm

-- 추이: kernel은 자동 추이.
theorem Lens.equiv_trans {α : Type} (L : Lens α) {x y z : Raw} :
    L.equiv x y → L.equiv y z → L.equiv x z := Eq.trans

-- 즉 Lens.equiv 은 자동 동치관계.
-- Lean의 == 에서 특별히 빌려온 게 아니라,
-- 함수 kernel이라는 수학 일반 구조에서 공짜.
instance {α : Type} (L : Lens α) : Equivalence (L.equiv) where
  refl  := L.equiv_refl
  symm  := L.equiv_symm
  trans := L.equiv_trans

-- ═══ 다른 Lens = 다른 등호 ═══

-- depth 렌즈로는 같음.
example : aab₀ =[Lens.depth] bab₀ := by decide

-- leaves 렌즈로도 같음.
example : aab₀ =[Lens.leaves] bab₀ := by decide

-- nodes 렌즈로도 같음.
example : aab₀ =[Lens.nodes] bab₀ := by decide

-- id' 렌즈로는 다름 (객체 자체).
example : ¬ (aab₀ =[Lens.id'] bab₀) := by
  unfold Lens.equiv; simp [lens_id_view]; decide

-- leftmost 렌즈로는 다름 (서로 다른 원자로 시작).
example : ¬ (aab₀ =[Lens.leftmost] bab₀) := by decide

-- ═══ 가장 거친 Lens: 상수 Bool ═══

-- 모든 Raw를 true로. Kernel = 전체 (모두 같음).
def Lens.constTrue : Lens Bool :=
  ⟨fun _ => true, fun _ _ => true⟩

-- 어떤 두 Raw든 이 렌즈로는 "같다."
theorem Lens.constTrue_equiv_all (x y : Raw) :
    x =[Lens.constTrue] y := by
  simp [Lens.equiv, Lens.view]
  induction x with
  | atom _ => induction y with
    | atom _ => rfl
    | rel a b iha ihb => simp [Raw.fold]
  | rel a b iha _ => induction y with
    | atom _ => simp [Raw.fold]
    | rel c d ihc _ => simp [Raw.fold]

-- ═══ id' 렌즈: 가장 섬세한 kernel ═══

-- id' kernel = 표준 =.
theorem Lens.id_equiv_iff_eq (x y : Raw) :
    (x =[Lens.id'] y) ↔ x = y := by
  simp [Lens.equiv, lens_id_view]

-- ═══ Kernel 거칠기 비교 ═══

-- Lens L이 Lens M보다 "섬세하다"면 L의 kernel ⊆ M의 kernel.
def Lens.refines {α β : Type} (L : Lens α) (M : Lens β) : Prop :=
  ∀ x y, L.equiv x y → M.equiv x y

-- id' 가 가장 섬세. 모든 Lens가 id' 의 조정 (refinement) 위에 있음.
theorem Lens.id_refines_all {α : Type} (M : Lens α) :
    Lens.id'.refines M := by
  intro x y h
  rw [Lens.id_equiv_iff_eq] at h
  simp [Lens.equiv, h]

-- constTrue 가 가장 거침. 모든 Lens가 constTrue 보다 섬세.
theorem Lens.refines_constTrue {α : Type} (L : Lens α) :
    L.refines Lens.constTrue :=
  fun x y _ => Lens.constTrue_equiv_all x y

-- ═══ 요약 ═══

-- | Lens      | kernel 크기 | "같다"의 정밀도 |
-- |-----------|------------|---------------|
-- | constTrue | 전체 Raw²  | 가장 거침 (모두 같음) |
-- | depth     | 부분집합   | 깊이가 같은 쌍 |
-- | nodes     | 부분집합   | 크기가 같은 쌍 |
-- | id'       | 대각선     | 가장 섬세 (자기 자신만) |

-- 정리 9의 순환 해결:
-- 이전 Equiv.lean은 Raw.equiv := (· = ·) 로 Lean 의 == 을 그대로 복제.
-- 이제 Lens.id'.equiv = (· = ·) 로 재해석.
-- 다른 Lens는 kernel 이 다름 → 서로 다른 공리계의 서로 다른 등호.
-- 세 성질 (refl, symm, trans) 이 함수 kernel 일반 사실에서 자동.
-- Lean 의 == 에 의존하는 게 아니라 수학 구조 자체에서.
