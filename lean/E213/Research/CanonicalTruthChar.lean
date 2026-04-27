import E213.Research.SemanticAtom

/-!
# Research.CanonicalTruthChar: Exact characterization of canonicalTruthMap

The meaning of `SemanticAtom.canonicalTruthMap : Raw → Prop`
(Xor-based): what determines the truth value of each Raw?

**Result**: `canonicalTruthMap r ↔ (a count of r) is odd`.

That is, the universal morphism of the Prop instance extracts
exactly *the a-count parity of Raw*.  The exact form of the
self-application of the semantic atom.

## Construction

Bool-valued analog: `aCountParityLens : Lens Bool := ⟨true, false,
xor⟩`.  view r = a-count parity (true iff odd).

And canonicalTruthMap r is the Prop translation of
(aCountParityLens.view r = true).
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

/-! ### Characterization of the Iff alternative

The exact meaning of `canonicalIffMap` (note 76 alternative):
`canonicalIffMap r ↔ b-count of r is even`.

The Iff XNOR fold extracts the b-count parity (dual to
the a-count odd of canonicalTruthMap). -/

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

/-- **The morphisms of two Prop instances differ**: the results of
    canonicalTruthMap (Xor) and canonicalIffMap (Iff) differ at a
    specific witness.  Different connective choices extract different
    algebraic invariants. -/
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
    iffBoolLens.view r = true`.  The algebraic content of the
    Iff XNOR fold. -/
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

And combine is very weak — T ∧ F = F.  The result is False for
most r.  Hypothesis: `canonicalAndMap r ↔ r = Raw.a`. -/

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

Or is the dual of And.  T ∨ F = T, F ∨ F = F.  Hypothesis:
`canonicalOrMap r ↔ r ≠ Raw.b` (= ∃ a leaf in r). -/

/-- Helper: the result of Raw.slash differs from Raw.b — depth-based. -/
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
        -- (slash x y h) ≠ b → at least one branch ≠ b → canonicalOrMap by IH.
        -- Since x ≠ y, both cannot simultaneously be b.  At least one ≠ b.
        by_cases hx : x = Raw.b
        · -- x = b, then y ≠ b (since x ≠ y).
          have hy_ne_b : y ≠ Raw.b := by
            intro heq; rw [heq] at h; exact h hx
          right
          exact ihy.mpr hy_ne_b
        · left
          exact ihx.mpr hx

end E213.Research.CanonicalTruthChar
