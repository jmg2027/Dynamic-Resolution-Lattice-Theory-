import E213.Hypervisor.LensKernel

/-
  실험: "같다" 를 공리로 추가하면 어떻게 되는가?

  답: 공리계에 = 을 primitive 로 추가 = **렌즈의 kernel 을 quotient 로 만들기.**
  구체:
    Lens L 선택 → LensQuot L 형성 → L.equiv 동일하게 취급.

  결과:
    - LensQuot Lens.depth ≃ Nat (depth 값으로 같다).
    - LensQuot Lens.atomSet ≃ Fin 3 의 부분집합들.
    - LensQuot Lens.id'    ≃ Raw (완전 구별).
    - LensQuot Lens.constTrue ≃ Unit (모두 같다).

  의미:
    각 공리계 = 렌즈 선택 + 그 kernel 을 = 으로 공리화한 quotient.
    PA = depth quotient. ZF (유사) = atomSet quotient 이상. Trivial = constTrue.

  "= 을 공리로 추가" 에 새로운 정보 없음.
  이미 렌즈 kernel 이 정의한 것을 primitive 로 부르는 것뿐.
-/

-- ═══ Lens 기반 Setoid ═══

def Lens.setoid {α : Type} (L : Lens α) : Setoid Raw where
  r := L.equiv
  iseqv := ⟨L.equiv_refl, L.equiv_symm, L.equiv_trans⟩

-- ═══ Raw quotient by Lens kernel ═══

def LensQuot {α : Type} (L : Lens α) : Type :=
  Quotient L.setoid

-- Embedding.
def LensQuot.mk {α : Type} (L : Lens α) : Raw → LensQuot L :=
  Quotient.mk L.setoid

-- Canonical value in α.
def LensQuot.value {α : Type} (L : Lens α) : LensQuot L → α :=
  Quotient.lift L.view (fun _ _ h => h)

-- value ∘ mk = L.view.
theorem LensQuot.value_mk {α : Type} (L : Lens α) (x : Raw) :
    LensQuot.value L (LensQuot.mk L x) = L.view x := rfl

-- ═══ 구체 예: depth quotient ═══

-- aab₀ 와 bab₀ 는 depth 가 같음 (둘 다 2).
-- depth 공리계 에서는 같은 "수."
example :
    LensQuot.mk Lens.depth aab₀ = LensQuot.mk Lens.depth bab₀ := by
  apply Quotient.sound
  show Lens.depth.equiv aab₀ bab₀
  decide

-- 하지만 id' quotient 에서는 다름.
example :
    LensQuot.mk Lens.id' aab₀ ≠ LensQuot.mk Lens.id' bab₀ := by
  intro h
  have := Quotient.exact h
  show False
  rw [show (Lens.id'.equiv aab₀ bab₀) = (Lens.id'.view aab₀ = Lens.id'.view bab₀)
      from rfl, lens_id_view, lens_id_view] at this
  exact absurd this (by decide)

-- ═══ 구체 예: constTrue quotient (모두 같다) ═══

-- constTrue 는 모든 Raw 를 true 로 보냄.
-- 따라서 모든 Raw 가 같은 LensQuot.
example :
    LensQuot.mk Lens.constTrue a₀ = LensQuot.mk Lens.constTrue b₀ := by
  apply Quotient.sound
  exact Lens.constTrue_equiv_all a₀ b₀

-- 모든 쌍이 같음 — trivial 공리계.
theorem constTrue_quot_trivial (x y : Raw) :
    LensQuot.mk Lens.constTrue x = LensQuot.mk Lens.constTrue y := by
  apply Quotient.sound
  exact Lens.constTrue_equiv_all x y

-- ═══ 실험 결과 해석 ═══

-- "같다 를 공리로 추가" = LensQuot 형성.
-- 각 렌즈마다 다른 공리계:
--   Lens.id'       → Raw 자체 (Peano 와 같은 수준).
--   Lens.depth     → Nat (수의 수학).
--   Lens.atomSet   → Finset (집합의 수학).
--   Lens.constTrue → Unit (자명 수학).

-- → "같다" 는 새로운 공리가 아니라 **렌즈 선택의 명시.**
-- 모든 공리계가 이미 렌즈 kernel 위에 있음.
-- quotient 는 그 kernel 을 primitive 로 부를 뿐.
