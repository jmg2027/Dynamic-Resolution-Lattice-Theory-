import E213.Hypervisor.Fold

/-
  Fold의 단사성: 수는 원리적으로 불완전한 렌즈.

  질문: 어떤 (α, g, h)가 fold : Raw → α 를 단사로 만드는가?

  답:
    1. h가 commutative이면 절대 단사 불가.
       rel x y ≠ rel y x (객체는 다름) 이지만 fold는 같음.
    2. α = Raw, g = .atom, h = .rel이면 fold = 항등 → 단사.
       하지만 이건 "수"가 아니라 "객체 자체."
    3. 통상 "수" (ℕ, ℤ 같이 commutative 구조)로는 단사 불가.

  결론: 등호 있는 codomain으로 등호 없는 domain을 완전히 볼 수 없다.
        수는 원리적 정보 손실.
-/

-- ═══ 정리 1: commutative h → fold 단사 불가 ═══

theorem fold_not_injective_of_comm {α : Type}
    (g : Fin 3 → α) (h : α → α → α)
    (hcomm : ∀ a b, h a b = h b a) :
    ¬ Function.Injective (Raw.fold g h) := by
  intro hinj
  -- rel a₀ b₀ 과 rel b₀ a₀ 는 다른 Raw.
  have hne : Raw.rel a₀ b₀ ≠ Raw.rel b₀ a₀ := by
    simp; exact a_ne_b
  -- 하지만 commutative h 하에서 fold 값은 같음.
  have heq : (Raw.rel a₀ b₀).fold g h = (Raw.rel b₀ a₀).fold g h :=
    fold_comm g h hcomm a₀ b₀
  exact hne (hinj heq)

-- ═══ 정리 2: 항등 fold는 단사 ═══

-- α = Raw, g = .atom, h = .rel: fold = identity.
theorem fold_atom_rel_id (x : Raw) :
    x.fold Raw.atom Raw.rel = x := by
  induction x with
  | atom i => rfl
  | rel a b iha ihb => simp [Raw.fold, iha, ihb]

theorem identity_fold_injective :
    Function.Injective (Raw.fold (α := Raw) Raw.atom Raw.rel) := by
  intro x y hxy
  rw [fold_atom_rel_id, fold_atom_rel_id] at hxy
  exact hxy

-- ═══ 따름정리: 통상 수 체계로는 단사 불가 ═══

-- ℕ의 덧셈은 commutative → leaves, nodes는 단사 아님.
example : ¬ Function.Injective Raw.leaves := by
  intro hinj
  have : Function.Injective
      (Raw.fold (fun _ => 1) (· + ·)) := by
    intro x y hxy
    apply hinj
    rw [leaves_as_fold, leaves_as_fold]; exact hxy
  exact fold_not_injective_of_comm _ _ Nat.add_comm this

-- ℕ의 max도 commutative → depth도 단사 아님.
example : ¬ Function.Injective Raw.depth := by
  intro hinj
  have : Function.Injective
      (Raw.fold (fun _ => 0) (fun a b => 1 + max a b)) := by
    intro x y hxy
    apply hinj
    rw [depth_as_fold, depth_as_fold]; exact hxy
  refine fold_not_injective_of_comm _ _ ?_ this
  intro a b; rw [Nat.max_comm]

-- ═══ 해석 ═══

-- 1. 비대칭 h는 단사 가능 (예: h = .rel, α = Raw).
-- 2. 그러나 그건 "수"가 아니라 객체를 그대로 들고 있는 것.
-- 3. 상용 수 구조 (ℕ, +, max) 는 commutative → 단사 불가.
--
-- 수학적 함의:
--   "수"란 commutative 구조 위에서 정의되는 것.
--   / 는 비대칭 (rel x y ≠ rel y x).
--   둘 사이의 구조적 불일치 → 정보 손실 필연.
--
-- 213의 관점:
--   바닥 (≠의 폭발)은 비대칭.
--   위로 가면서 (fold를 통해) 수가 됨 — 대칭 잃음.
--   / 한 번 = 정보 1 bit 생성.
--   수 한 개 뽑기 = 일부 bit 폐기.
--
-- 이 정리는 "수는 원리적으로 불완전한 렌즈"의 Lean 증거.
