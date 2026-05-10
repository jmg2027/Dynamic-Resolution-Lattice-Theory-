import E213.Lens.SemanticAtom
import E213.Lens.Instances.Reach
import E213.Lens.EqPW

/-!
# LensOnLens: Lens itself as an instance of the semantic framework

Mechanical proof of the thesis of Note 53 ("no meta-hierarchy —
Lens is another instance within the framework").

This file deliberately avoids constructing a `HasDistinguishing
(Lens α)` instance: that field's `combine_sym` is a `Lens α`-equality
which requires funext on the inner combine field — i.e., it is the
canonical Cat 1 Quot.sound source.  Instead we build the universal
morphism `Raw → Lens α` directly via `Raw.fold` and provide eqPW
companions for kernel-level reasoning.

## Significance

The sharpest form of the framework's self-cover:
- Lens is an instance of the output type, *not* an element (Raw) of
  the framework.
- The Lens type itself is an instance of the same framework
  abstraction (HasDistinguishing) at the *kernel* level (= up to eqPW),
  with the bridge to strict `=` requiring one isolated funext that we
  refuse to introduce.
- → No meta-hierarchy — Lens-on-Lens is *not* a new layer.

universalMorphism (Lens Bool) : Raw → Lens Bool — elements of Raw
map to Lenses.  The exact form of self-application of a semantic
atom.
-/

namespace E213.Lens.Compose.OnLens

open E213.Theory E213.Lens
open E213.Lens.SemanticAtom

/-- Constant-true Lens. -/
def constTrueLens : Lens Bool := ⟨true, true, fun _ _ => true⟩

/-- Constant-false Lens. -/
def constFalseLens : Lens Bool := ⟨false, false, fun _ _ => false⟩

/-- The two constant Lenses are distinct. -/
theorem const_lenses_distinct : constTrueLens ≠ constFalseLens := by
  intro h
  have h_base_a : constTrueLens.base_a = constFalseLens.base_a :=
    congrArg Lens.base_a h
  exact Bool.noConfusion h_base_a

end E213.Lens.Compose.OnLens

namespace E213.Lens.Compose.OnLens

open E213.Theory E213.Lens
open E213.Lens.SemanticAtom

/-- Pointwise xor combine of Lenses. -/
def lensXor (L M : Lens Bool) : Lens Bool :=
  ⟨xor L.base_a M.base_a, xor L.base_b M.base_b,
   fun x y => xor (L.combine x y) (M.combine x y)⟩

/-- Pointwise (eqPW) commutativity of `lensXor`.  ∅-axiom — replaces
    the funext-bearing `lensXor L M = lensXor M L` (which is what the
    DIRTY `combine_sym` field of a hypothetical `HasDistinguishing
    (Lens Bool)` would require). -/
theorem lensXor_comm_eqPW (L M : Lens Bool) :
    (lensXor L M).eqPW (lensXor M L) := by
  refine ⟨?_, ?_, ?_⟩
  · show xor L.base_a M.base_a = xor M.base_a L.base_a
    cases L.base_a <;> cases M.base_a <;> rfl
  · show xor L.base_b M.base_b = xor M.base_b L.base_b
    cases L.base_b <;> cases M.base_b <;> rfl
  · intro x y
    show xor (L.combine x y) (M.combine x y) = xor (M.combine x y) (L.combine x y)
    cases L.combine x y <;> cases M.combine x y <;> rfl

/-- `lensXor` is eqPW-congruent in both arguments. -/
theorem lensXor_eqPW_cong (L1 L2 M1 M2 : Lens Bool)
    (hL : L1.eqPW L2) (hM : M1.eqPW M2) :
    (lensXor L1 M1).eqPW (lensXor L2 M2) := by
  refine ⟨?_, ?_, ?_⟩
  · show xor L1.base_a M1.base_a = xor L2.base_a M2.base_a
    rw [hL.1, hM.1]
  · show xor L1.base_b M1.base_b = xor L2.base_b M2.base_b
    rw [hL.2.1, hM.2.1]
  · intro x y
    show xor (L1.combine x y) (M1.combine x y)
       = xor (L2.combine x y) (M2.combine x y)
    rw [hL.2.2 x y, hM.2.2 x y]

end E213.Lens.Compose.OnLens

namespace E213.Lens.Compose.OnLens

open E213.Theory E213.Lens
open E213.Lens.SemanticAtom

/-! ### Universal morphism Raw → Lens Bool -/

/-- Universal morphism Raw → Lens Bool, defined directly via `Raw.fold`
    (no HasDistinguishing instance required at the `Lens Bool` level). -/
def lensUniversalMorphism : Raw → Lens Bool :=
  Raw.fold constTrueLens constFalseLens lensXor

theorem lensUniversalMorphism_a :
    lensUniversalMorphism Raw.a = constTrueLens := rfl

theorem lensUniversalMorphism_b :
    lensUniversalMorphism Raw.b = constFalseLens := rfl

/-- Pointwise (eqPW) slash compatibility of the universal morphism. -/
theorem lensUniversalMorphism_slash_eqPW (x y : Raw) (h : x ≠ y) :
    (lensUniversalMorphism (Raw.slash x y h)).eqPW
      (lensXor (lensUniversalMorphism x) (lensUniversalMorphism y)) := by
  unfold lensUniversalMorphism
  exact Lens.fold_slash_eqPW _ _ _ lensXor_comm_eqPW x y h

end E213.Lens.Compose.OnLens

namespace E213.Lens.Compose.OnLens

open E213.Theory E213.Lens
open E213.Lens.SemanticAtom

/-! ### Generic Lens-on-Lens (recursive self-application) -/

/-- Constant Lens — view is always the same element. -/
def constLens {α : Type} (a : α) : Lens α := ⟨a, a, fun _ _ => a⟩

/-- Two constant Lenses are distinguishable iff their bases are distinguishable. -/
theorem constLens_distinct {α : Type} {x y : α} (h : x ≠ y) :
    constLens x ≠ constLens y := by
  intro heq
  have : (constLens x).base_a = (constLens y).base_a := congrArg Lens.base_a heq
  exact h this

/-- Generic Lens combine using the combine of α. -/
def lensCombineGeneric {α : Type} (c : α → α → α) (L M : Lens α) : Lens α :=
  ⟨c L.base_a M.base_a, c L.base_b M.base_b,
   fun x y => c (L.combine x y) (M.combine x y)⟩

/-- Pointwise (eqPW) commutativity of `lensCombineGeneric`. -/
theorem lensCombineGeneric_comm_eqPW {α : Type} (c : α → α → α)
    (hsym : ∀ u v, c u v = c v u) (L M : Lens α) :
    (lensCombineGeneric c L M).eqPW (lensCombineGeneric c M L) := by
  refine ⟨?_, ?_, ?_⟩
  · exact hsym _ _
  · exact hsym _ _
  · intro x y; exact hsym _ _

/-- `lensCombineGeneric c` is eqPW-congruent in both arguments. -/
theorem lensCombineGeneric_eqPW_cong {α : Type} (c : α → α → α)
    (L1 L2 M1 M2 : Lens α)
    (hL : L1.eqPW L2) (hM : M1.eqPW M2) :
    (lensCombineGeneric c L1 M1).eqPW (lensCombineGeneric c L2 M2) := by
  refine ⟨?_, ?_, ?_⟩
  · show c L1.base_a M1.base_a = c L2.base_a M2.base_a
    rw [hL.1, hM.1]
  · show c L1.base_b M1.base_b = c L2.base_b M2.base_b
    rw [hL.2.1, hM.2.1]
  · intro x y
    show c (L1.combine x y) (M1.combine x y) = c (L2.combine x y) (M2.combine x y)
    rw [hL.2.2 x y, hM.2.2 x y]

end E213.Lens.Compose.OnLens

namespace E213.Lens.Compose.OnLens

open E213.Theory E213.Lens
open E213.Lens.SemanticAtom
open E213.Lens.Instances.Reach

/-! ### Universal morphisms at higher levels (direct Raw.fold) -/

/-- Raw → Lens (Lens Bool) universal morphism. -/
def universalMorphismLevelTwo : Raw → Lens (Lens Bool) :=
  Raw.fold (constLens (constLens true)) (constLens (constLens false))
           (lensCombineGeneric (lensCombineGeneric and))

/-- Raw → Lens (Lens (Lens Bool)) universal morphism. -/
def universalMorphismLevelThree : Raw → Lens (Lens (Lens Bool)) :=
  Raw.fold (constLens (constLens (constLens true)))
           (constLens (constLens (constLens false)))
           (lensCombineGeneric (lensCombineGeneric (lensCombineGeneric and)))

end E213.Lens.Compose.OnLens
