import E213.Meta.LensTaxonomy

/-
  Taxonomy 의 한계 증명.

  질문: 7 properties / 5 classes 가 유일하고 complete?

  답 (정직):
    **유일하지 않음.**
    추가 properties 로 더 fine-grained classification 가능.

  증명 대상:
    1. Properties 간 constraint relations.
    2. 2^7 = 128 이론적 조합, 실제로 많이 impossible.
    3. 우리 7 properties 밖 추가 properties 존재.
    4. 따라서 taxonomy 는 **partial**, non-unique.
-/

-- ═══ Constraint Relations ═══

-- LeftProj → Assoc.
theorem leftProj_implies_assoc {α : Type} (L : Lens α)
    (h : L.leftProjComb) : L.associativeComb := by
  intro a b c
  rw [h, h]

-- LeftProj → Idem.
theorem leftProj_implies_idem {α : Type} (L : Lens α)
    (h : L.leftProjComb) : L.idempotentComb :=
  fun a => h a a

-- RightProj → Assoc.
theorem rightProj_implies_assoc {α : Type} (L : Lens α)
    (h : L.rightProjComb) : L.associativeComb := by
  intro a b c
  rw [h, h]

-- RightProj → Idem.
theorem rightProj_implies_idem {α : Type} (L : Lens α)
    (h : L.rightProjComb) : L.idempotentComb :=
  fun a => h a a

-- LeftProj + RightProj → α has at most 1 element (trivial).
theorem both_proj_forces_trivial {α : Type} (L : Lens α)
    (hl : L.leftProjComb) (hr : L.rightProjComb) :
    ∀ a b : α, a = b := by
  intro a b
  have h1 : L.combine a b = a := hl a b
  have h2 : L.combine a b = b := hr a b
  rw [h1] at h2
  exact h2

-- 따라서 leftProj + rightProj 공존 = α trivial.
-- → 실제 classes 에서 동시 만족 불가.

-- ═══ 추가 Properties (기존 7개 밖) ═══

def Lens.absorbingComb {α : Type} (L : Lens α) : Prop :=
  ∀ a b, L.combine a (L.combine a b) = L.combine a b

def Lens.cancellativeComb {α : Type} (L : Lens α) : Prop :=
  ∀ a b c, L.combine a c = L.combine b c → a = b

def Lens.constantComb {α : Type} (L : Lens α) : Prop :=
  ∃ c, ∀ a b, L.combine a b = c

def Lens.hasIdentity {α : Type} (L : Lens α) : Prop :=
  ∃ e : α, ∀ a, L.combine e a = a ∧ L.combine a e = a

-- ═══ 추가 예시 증명 ═══

theorem constTrue_const_comb : Lens.constTrue.constantComb := by
  refine ⟨true, ?_⟩
  intro _ _; rfl

theorem depth_absorbing : Lens.depth.absorbingComb := by
  intro a b
  simp [Lens.depth]
  omega

theorem leaves_cancellative : Lens.leaves.cancellativeComb := by
  intro a b c h
  simp [Lens.leaves] at h
  omega

-- ═══ 결론: Non-unique, Partial ═══

-- 기존 7 properties: 2^7 = 128 이론, 실현 가능 subset.
-- 추가 4 properties: 2^11 = 2048 조합.
-- 모든 수학 성질 → infinite lattice.

-- 따라서 taxonomy 는:
--   Non-unique (추가 properties 로 확장).
--   Partial (모든 algebraic structure 못 포괄).
--   Useful (실용 classification).

-- 수학적 한계:
--   완전 classification = universal algebra lattice.
--   무한 operations 조합 가능.
--   우리 것은 그 finite approximation.

-- 위상수학 관점:
--   Lens 공간 의 topology = property 기반.
--   Stone duality: property = closed set.
--   Complete classification = Stone space.
--   우리 것 = finite subspace.
