import E213.Meta.LensHomeo

/-
  Lens Taxonomy: 렌즈가 가질 수 있는 형태 의 수학적 분류.

  구조 (g : Fin 3 → α, h : α → α → α) 로부터 결정되는 성질들:

  atomValue 관점 (g):
    - constantAtom: 모든 atom 같은 값.
    - injectiveAtom: 다른 atom → 다른 값.

  combine 관점 (h):
    - commutativeComb: h a b = h b a.
    - associativeComb.
    - idempotentComb: h a a = a.
    - leftProj: h a _ = a.
    - rightProj: h _ b = b.
    - constantComb: h _ _ = c.

  Lens 형태 = 이 성질들의 조합.
-/

-- ═══ atomValue 성질 ═══

def Lens.constantAtom {α : Type} (L : Lens α) : Prop :=
  ∀ i j : Fin 3, L.atomValue i = L.atomValue j

def Lens.injectiveAtom {α : Type} (L : Lens α) : Prop :=
  Function.Injective L.atomValue

-- ═══ combine 성질 ═══

def Lens.commutativeComb {α : Type} (L : Lens α) : Prop :=
  ∀ a b : α, L.combine a b = L.combine b a

def Lens.associativeComb {α : Type} (L : Lens α) : Prop :=
  ∀ a b c : α, L.combine (L.combine a b) c = L.combine a (L.combine b c)

def Lens.idempotentComb {α : Type} (L : Lens α) : Prop :=
  ∀ a : α, L.combine a a = a

def Lens.leftProjComb {α : Type} (L : Lens α) : Prop :=
  ∀ a b : α, L.combine a b = a

def Lens.rightProjComb {α : Type} (L : Lens α) : Prop :=
  ∀ a b : α, L.combine a b = b

-- ═══ 분류: 각 기존 lens 의 profile ═══

-- Lens.depth: atom const (→ 0), comm, assoc, idempotent (1+max).
theorem depth_const_atom : Lens.depth.constantAtom :=
  fun _ _ => rfl

theorem depth_comm : Lens.depth.commutativeComb :=
  fun a b => by simp [Lens.depth, Nat.max_comm]

theorem depth_assoc : Lens.depth.associativeComb :=
  fun a b c => by simp [Lens.depth]; omega

theorem depth_idem : Lens.depth.idempotentComb :=
  fun a => by simp [Lens.depth]

-- Lens.leaves: atom const (→ 1), comm, assoc (+), not idem.
theorem leaves_const_atom : Lens.leaves.constantAtom :=
  fun _ _ => rfl

theorem leaves_comm : Lens.leaves.commutativeComb :=
  fun a b => by simp [Lens.leaves]; omega

theorem leaves_assoc : Lens.leaves.associativeComb :=
  fun a b c => by simp [Lens.leaves]; omega

-- leaves 는 idempotent 아님: 1+1 = 2 ≠ 1.
example : ¬ Lens.leaves.idempotentComb := by
  intro h
  have := h 1
  simp [Lens.leaves] at this

-- Lens.leftSpine: not comm, not assoc, but leftProj-ish.
theorem leftSpine_not_comm : ¬ Lens.leftSpine.commutativeComb := by
  intro h
  have := h 0 1
  simp [Lens.leftSpine] at this

-- Lens.Z3: atom inj (identity), comm (add mod 3).
theorem Z3_inj_atom : Lens.Z3.injectiveAtom := by
  intro i j h
  simp [Lens.Z3] at h
  exact h

theorem Z3_comm : Lens.Z3.commutativeComb := by
  intro a b
  simp [Lens.Z3, Fin3.add]
  ext
  omega

-- Lens.signed: atom inj, not comm (subtraction).
theorem signed_not_comm : ¬ Lens.signed.commutativeComb := by
  intro h
  have h01 := h 1 (-1)
  simp [Lens.signed] at h01
  omega

-- Lens.constTrue: atom const, comm, assoc, idem.
theorem constTrue_const_atom : Lens.constTrue.constantAtom :=
  fun _ _ => rfl

theorem constTrue_comm : Lens.constTrue.commutativeComb :=
  fun _ _ => rfl

theorem constTrue_idem : Lens.constTrue.idempotentComb :=
  fun _ => rfl

-- Lens.id': atom inj-ish (Fin 3 → Raw via atom, inj).
theorem id_inj_atom : Lens.id'.injectiveAtom := by
  intro i j h
  simp [Lens.id'] at h
  exact h

-- id' combine = rel: not comm (rel x y ≠ rel y x).
theorem id_not_comm : ¬ Lens.id'.commutativeComb := by
  intro h
  have := h a₀ b₀
  simp [Lens.id'] at this

-- ═══ 종합 분류 표 ═══

-- | Lens       | constAtom | injAtom | comm | assoc | idem |
-- |------------|-----------|---------|------|-------|------|
-- | depth      |     ✓    |    ✗   |  ✓  |   ✓  |  ✓  |
-- | leaves     |     ✓    |    ✗   |  ✓  |   ✓  |  ✗  |
-- | nodes      |     ✓    |    ✗   |  ✓  |   ✓  |  ✗  |
-- | leftSpine  |     ✓    |    ✗   |  ✗  |   ✗  |  ✗  |
-- | Z3         |     ✗    |    ✓   |  ✓  |   ✓  |  ✗  |
-- | signed     |     ✗    |    ✓   |  ✗  |   ✗  |  ✗  |
-- | constTrue  |     ✓    |    ✗   |  ✓  |   ✓  |  ✓  |
-- | id'        |     ✗    |    ✓   |  ✗  |   ✗  |  ✗  |

-- ═══ 분류 체계 ═══

-- Class 1 (Ordered monoid): depth, leaves, nodes.
--   constAtom, comm, assoc, ±idem.
-- Class 2 (Commutative group): Z3.
--   injAtom, comm, assoc, inverses.
-- Class 3 (Projection): leftSpine, rightSpine.
--   constAtom, not comm/assoc.
-- Class 4 (Asymmetric): signed, id'.
--   injAtom, not comm.
-- Class 5 (Trivial): constTrue.
--   모든 성질 (universal collapse).
