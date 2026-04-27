import E213.Research.SemanticAtom

/-!
# Research.CanonicalTruthChar: canonicalTruthMap 의 정확 한 characterization

`SemanticAtom.canonicalTruthMap : Raw → Prop` (Xor-based) 의
의미: 각 Raw 의 truth value 가 무엇 으로 결정 되는가?

**결과**: `canonicalTruthMap r ↔ (a count of r) is odd`.

즉 Prop instance 의 universal morphism 이 정확히 *Raw 의 a-count
parity* 를 추출.  의미 atom 의 self-application 의 정확 한 form.

## 구성

Bool-valued analog: `aCountParityLens : Lens Bool := ⟨true, false,
xor⟩`.  view r = a-count parity (true iff odd).

그리고 canonicalTruthMap r = (aCountParityLens.view r = true)
의 Prop 변환.
-/

namespace E213.Research.CanonicalTruthChar

open E213.Firmware E213.Hypervisor
open E213.Research.SemanticAtom

/-- Bool-valued a-count parity Lens. -/
def aCountParityLens : Lens Bool := ⟨true, false, fun x y => xor x y⟩

theorem aCountParityLens_a : aCountParityLens.view Raw.a = true := rfl
theorem aCountParityLens_b : aCountParityLens.view Raw.b = false := rfl

theorem aCountParityLens_slash (x y : Raw) (h : x ≠ y) :
    aCountParityLens.view (Raw.slash x y h)
      = xor (aCountParityLens.view x) (aCountParityLens.view y) := by
  apply Raw.fold_slash
  intro u v
  show xor u v = xor v u
  cases u <;> cases v <;> rfl

end E213.Research.CanonicalTruthChar

namespace E213.Research.CanonicalTruthChar

open E213.Firmware E213.Hypervisor
open E213.Research.SemanticAtom

/-- canonicalTruthMap 의 specific reduction at a. -/
private theorem ctm_a : canonicalTruthMap Raw.a = True :=
  canonicalTruthMap_a

/-- canonicalTruthMap 의 specific reduction at b. -/
private theorem ctm_b : canonicalTruthMap Raw.b = False :=
  canonicalTruthMap_b

/-- propXor 의 Bool xor 와 의 connection. -/
theorem propXor_iff_bool_xor (P Q : Prop) (b₁ b₂ : Bool)
    (hP : P ↔ (b₁ = true)) (hQ : Q ↔ (b₂ = true)) :
    propXor P Q ↔ (xor b₁ b₂ = true) := by
  unfold propXor
  cases b₁ <;> cases b₂ <;> simp [xor, hP, hQ]

end E213.Research.CanonicalTruthChar

namespace E213.Research.CanonicalTruthChar

open E213.Firmware E213.Hypervisor
open E213.Research.SemanticAtom

/-- **Main characterization**: canonicalTruthMap r ↔ aCountParityLens.view r = true. -/
theorem canonicalTruthMap_iff_aCountOdd (r : Raw) :
    canonicalTruthMap r ↔ aCountParityLens.view r = true := by
  induction r using Raw.rec with
  | a =>
      rw [canonicalTruthMap_a, aCountParityLens_a]
      simp
  | b =>
      rw [canonicalTruthMap_b, aCountParityLens_b]
      simp
  | slash x y h ihx ihy =>
      rw [canonicalTruthMap_slash x y h, aCountParityLens_slash x y h]
      exact propXor_iff_bool_xor _ _ _ _ ihx ihy

end E213.Research.CanonicalTruthChar

namespace E213.Research.CanonicalTruthChar

open E213.Firmware E213.Hypervisor
open E213.Research.SemanticAtom

/-! ### Iff alternative 의 characterization

`canonicalIffMap` (note 76 alternative) 의 정확 한 의미:
`canonicalIffMap r ↔ b-count of r is even`.

Iff XNOR fold 가 b-count parity 추출 (canonicalTruthMap 의 a-count
odd 와 dual). -/

/-- Bool-valued Iff Lens. -/
def iffBoolLens : Lens Bool := ⟨true, false, fun x y => decide (x = y)⟩

theorem iffBoolLens_a : iffBoolLens.view Raw.a = true := rfl
theorem iffBoolLens_b : iffBoolLens.view Raw.b = false := rfl

theorem iffBoolLens_slash (x y : Raw) (h : x ≠ y) :
    iffBoolLens.view (Raw.slash x y h)
      = decide (iffBoolLens.view x = iffBoolLens.view y) := by
  apply Raw.fold_slash
  intro u v
  show decide (u = v) = decide (v = u)
  cases u <;> cases v <;> rfl

end E213.Research.CanonicalTruthChar

namespace E213.Research.CanonicalTruthChar

open E213.Firmware E213.Hypervisor
open E213.Research.SemanticAtom

/-- **두 Prop instance 의 morphism 이 다름**: canonicalTruthMap
    (Xor) 과 canonicalIffMap (Iff) 의 결과 가 specific witness
    에서 다름.  Connective 선택 에 따라 specific algebraic
    invariant 가 다름. -/
theorem canonicalTruthMap_ne_canonicalIffMap_witness :
    canonicalTruthMap (Raw.slash Raw.a Raw.b (by decide))
      ≠ canonicalIffMap (Raw.slash Raw.a Raw.b (by decide)) := by
  intro heq
  -- canonicalTruthMap (slash a b) = propXor True False (via a-count odd: 1).
  -- canonicalIffMap (slash a b) = (True ↔ False) (via b-count parity).
  have h₁ : canonicalTruthMap (Raw.slash Raw.a Raw.b (by decide))
              = propXor True False := by
    rw [canonicalTruthMap_slash, canonicalTruthMap_a, canonicalTruthMap_b]
  rw [h₁] at heq
  -- propXor True False holds (XOR of T, F = T).
  have h_xor : propXor True False := ⟨Or.inl trivial, fun ⟨_, hf⟩ => hf⟩
  rw [heq] at h_xor
  -- canonicalIffMap (slash a b) = (T ↔ F).  Direct simp through unfold.
  have hf : canonicalIffMap (Raw.slash Raw.a Raw.b (by decide))
              = (True ↔ False) := by
    unfold canonicalIffMap
    show @universalMorphism Prop propAsDistinguishingIff
            (Raw.slash Raw.a Raw.b (by decide)) = (True ↔ False)
    rw [universalMorphism_slash Prop (d := propAsDistinguishingIff)
          Raw.a Raw.b (by decide)]
    rfl
  rw [hf] at h_xor
  exact h_xor.mp trivial

theorem canonicalTruthMap_ne_canonicalIffMap :
    canonicalTruthMap ≠ canonicalIffMap := by
  intro heq
  exact canonicalTruthMap_ne_canonicalIffMap_witness (congrFun heq _)

end E213.Research.CanonicalTruthChar

namespace E213.Research.CanonicalTruthChar

open E213.Firmware E213.Hypervisor
open E213.Research.SemanticAtom

/-! ### Iff alternative characterization (b-count parity) -/

/-- Iff (P ↔ Q) ↔ Bool equality on (b₁ = true), (b₂ = true). -/
theorem iff_iff_bool_eq (P Q : Prop) (b₁ b₂ : Bool)
    (hP : P ↔ (b₁ = true)) (hQ : Q ↔ (b₂ = true)) :
    (P ↔ Q) ↔ (decide (b₁ = b₂) = true) := by
  cases b₁ <;> cases b₂ <;> simp [hP, hQ]

/-- **canonicalIffMap characterization**: `canonicalIffMap r ↔
    iffBoolLens.view r = true`.  Iff XNOR fold 의 algebraic
    content. -/
theorem canonicalIffMap_iff_iffBoolLens (r : Raw) :
    canonicalIffMap r ↔ iffBoolLens.view r = true := by
  induction r using Raw.rec with
  | a =>
      rw [canonicalIffMap_a, iffBoolLens_a]
      simp
  | b =>
      rw [canonicalIffMap_b, iffBoolLens_b]
      simp
  | slash x y h ihx ihy =>
      rw [canonicalIffMap_slash x y h, iffBoolLens_slash x y h]
      exact iff_iff_bool_eq _ _ _ _ ihx ihy

end E213.Research.CanonicalTruthChar

namespace E213.Research.CanonicalTruthChar

open E213.Firmware E213.Hypervisor
open E213.Research.SemanticAtom

/-! ### And-based characterization: r = Raw.a iff canonicalAndMap

And combine 가 매우 약 — T ∧ F = F.  대부분 r 에 대해 결과 가
False.  Hypothesis: `canonicalAndMap r ↔ r = Raw.a`. -/

theorem canonicalAndMap_iff_eq_a (r : Raw) :
    canonicalAndMap r ↔ r = Raw.a := by
  induction r using Raw.rec with
  | a =>
      rw [canonicalAndMap_a]
      simp
  | b =>
      rw [canonicalAndMap_b]
      constructor
      · intro h; exact absurd h (fun e => e)
      · intro heq; exact absurd heq (by decide)
  | slash x y h ihx ihy =>
      rw [canonicalAndMap_slash x y h]
      constructor
      · rintro ⟨hx_and, hy_and⟩
        have hx_eq : x = Raw.a := ihx.mp hx_and
        have hy_eq : y = Raw.a := ihy.mp hy_and
        rw [hx_eq, hy_eq] at h
        exact absurd rfl h
      · intro heq
        exact absurd heq (fun e => by
          -- Raw.slash x y h ≠ Raw.a (depth-based).
          have hview := congrArg Lens.depth.view e
          have hslash : Lens.depth.view (Raw.slash x y h)
                        = 1 + max (Lens.depth.view x) (Lens.depth.view y) := by
            apply Raw.fold_slash
            intro u v
            show 1 + max u v = 1 + max v u
            rw [Nat.max_comm]
          rw [hslash] at hview
          have h_a : Lens.depth.view Raw.a = 0 := rfl
          rw [h_a] at hview
          omega)

end E213.Research.CanonicalTruthChar

namespace E213.Research.CanonicalTruthChar

open E213.Firmware E213.Hypervisor
open E213.Research.SemanticAtom

/-! ### Or-based characterization: r ≠ Raw.b iff canonicalOrMap

Or 가 And 의 dual.  T ∨ F = T, F ∨ F = F.  Hypothesis:
`canonicalOrMap r ↔ r ≠ Raw.b` (= ∃ a leaf in r). -/

/-- Helper: Raw.slash 의 결과 가 Raw.b 와 다름 — depth-based. -/
private theorem slash_ne_b_via_depth (x y : Raw) (h : x ≠ y) :
    Raw.slash x y h ≠ Raw.b := by
  intro heq
  have hview := congrArg Lens.depth.view heq
  have hslash : Lens.depth.view (Raw.slash x y h)
                = 1 + max (Lens.depth.view x) (Lens.depth.view y) := by
    apply Raw.fold_slash
    intro u v
    show 1 + max u v = 1 + max v u
    rw [Nat.max_comm]
  rw [hslash] at hview
  have h_b : Lens.depth.view Raw.b = 0 := rfl
  rw [h_b] at hview
  omega

theorem canonicalOrMap_iff_ne_b (r : Raw) :
    canonicalOrMap r ↔ r ≠ Raw.b := by
  induction r using Raw.rec with
  | a =>
      rw [canonicalOrMap_a]
      constructor
      · intro _ heq; exact absurd heq (by decide)
      · intro _; trivial
  | b =>
      rw [canonicalOrMap_b]
      constructor
      · intro h; exact absurd h (fun e => e)
      · intro hne; exact absurd rfl hne
  | slash x y h ihx ihy =>
      rw [canonicalOrMap_slash x y h]
      constructor
      · intro _ hslash_eq_b
        exact slash_ne_b_via_depth x y h hslash_eq_b
      · intro _
        -- (slash x y h) ≠ b → 적어도 하나 의 branch 가 ≠ b → IH 로 canonicalOrMap.
        -- x ≠ y 이므로 둘 다 동시 에 b 가 부재.  적어도 하나 가 ≠ b.
        by_cases hx : x = Raw.b
        · -- x = b, then y ≠ b (since x ≠ y).
          have hy_ne_b : y ≠ Raw.b := by
            intro heq; rw [heq] at h; exact h hx
          right
          exact ihy.mpr hy_ne_b
        · left
          exact ihx.mpr hx

end E213.Research.CanonicalTruthChar
