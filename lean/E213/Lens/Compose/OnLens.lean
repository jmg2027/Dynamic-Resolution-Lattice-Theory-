import E213.Lens.SemanticAtom
import E213.Lens.Instances.Reach

/-!
# LensOnLens: Lens itself as an instance of the semantic framework

Mechanical proof of the thesis of Note 53 ("no meta-hierarchy —
Lens is another instance within the framework").

Defines a `HasDistinguishing (Lens Bool)` instance — two distinct
Lenses (constTrueLens, constFalseLens) + pointwise xor combine.

## Significance

The sharpest form of the framework's self-cover:
- Lens is an instance of the output type, *not* an element (Raw) of
  the framework.
- The Lens type itself is an instance of the same framework
  abstraction (HasDistinguishing).
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

theorem lensXor_comm (L M : Lens Bool) : lensXor L M = lensXor M L := by
  unfold lensXor
  -- Structural equality on Lens record.
  congr 1
  · cases L.base_a <;> cases M.base_a <;> rfl
  · cases L.base_b <;> cases M.base_b <;> rfl
  · funext x y
    cases L.combine x y <;> cases M.combine x y <;> rfl

end E213.Lens.Compose.OnLens

namespace E213.Lens.Compose.OnLens

open E213.Theory E213.Lens
open E213.Lens.SemanticAtom

/-- **Lens-on-Lens**: Lens Bool itself is a HasDistinguishing instance. -/
def lensBoolHasDistinguishing : HasDistinguishing (Lens Bool) where
  a := constTrueLens
  b := constFalseLens
  distinct := const_lenses_distinct
  combine := lensXor
  combine_sym := lensXor_comm

end E213.Lens.Compose.OnLens

namespace E213.Lens.Compose.OnLens

open E213.Theory E213.Lens
open E213.Lens.SemanticAtom

/-! ### Universal morphism Raw → Lens Bool

The sharpest self-application instance — elements of Raw map to
Lenses (= the representation unit of the framework). -/

/-- Universal morphism Raw → Lens Bool via lens-on-lens instance. -/
def lensUniversalMorphism : Raw → Lens Bool :=
  @universalMorphism (Lens Bool) lensBoolHasDistinguishing

theorem lensUniversalMorphism_a :
    lensUniversalMorphism Raw.a = constTrueLens :=
  @universalMorphism_a (Lens Bool) lensBoolHasDistinguishing

theorem lensUniversalMorphism_b :
    lensUniversalMorphism Raw.b = constFalseLens :=
  @universalMorphism_b (Lens Bool) lensBoolHasDistinguishing

theorem lensUniversalMorphism_slash (x y : Raw) (h : x ≠ y) :
    lensUniversalMorphism (Raw.slash x y h)
      = lensXor (lensUniversalMorphism x) (lensUniversalMorphism y) :=
  @universalMorphism_slash (Lens Bool) lensBoolHasDistinguishing x y h

end E213.Lens.Compose.OnLens

namespace E213.Lens.Compose.OnLens

open E213.Theory E213.Lens
open E213.Lens.SemanticAtom

/-! ### Generic Lens-on-Lens: recursive self-application

Generic form of `HasDistinguishing α → HasDistinguishing (Lens α)`.
Yields an infinite tower `Lens α`, `Lens (Lens α)`,
`Lens (Lens (Lens α))`, ...

The *recursive closure* of the framework's self-application. -/

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

/-- Commutativity of α's combine implies commutativity of lensCombineGeneric. -/
theorem lensCombineGeneric_comm {α : Type} (c : α → α → α)
    (hsym : ∀ u v, c u v = c v u) (L M : Lens α) :
    lensCombineGeneric c L M = lensCombineGeneric c M L := by
  unfold lensCombineGeneric
  congr 1
  · exact hsym _ _
  · exact hsym _ _
  · funext x y; exact hsym _ _

end E213.Lens.Compose.OnLens

namespace E213.Lens.Compose.OnLens

open E213.Theory E213.Lens
open E213.Lens.SemanticAtom

/-- **Generic Lens-on-Lens**: `HasDistinguishing α → HasDistinguishing
    (Lens α)`.  The Lens type itself is an instance of the semantic
    framework.

    Recursive: this instance + automatic elaboration → enables an
    infinite tower of `Lens (Lens α)`, `Lens^n α`. -/
def lensHasDistinguishing (α : Type) [d : HasDistinguishing α] :
    HasDistinguishing (Lens α) where
  a := constLens d.a
  b := constLens d.b
  distinct := constLens_distinct d.distinct
  combine := lensCombineGeneric d.combine
  combine_sym := lensCombineGeneric_comm d.combine d.combine_sym

end E213.Lens.Compose.OnLens

namespace E213.Lens.Compose.OnLens

open E213.Theory E213.Lens
open E213.Lens.SemanticAtom
open E213.Lens.Instances.Reach

/-! ### Tower demonstration: infinite recursive instances

Recursive application of
`HasDistinguishing α → HasDistinguishing (Lens α)` —
Bool → Lens Bool → Lens (Lens Bool) → ...

The framework's self-application forms an *unbounded tower*. -/

/-- Level 1: HasDistinguishing (Lens Bool). -/
def levelOne : HasDistinguishing (Lens Bool) :=
  lensHasDistinguishing Bool (d := boolHasDistinguishing)

/-- Level 2: HasDistinguishing (Lens (Lens Bool)). -/
def levelTwo : HasDistinguishing (Lens (Lens Bool)) :=
  lensHasDistinguishing (Lens Bool) (d := levelOne)

/-- Level 3: HasDistinguishing (Lens (Lens (Lens Bool))). -/
def levelThree : HasDistinguishing (Lens (Lens (Lens Bool))) :=
  lensHasDistinguishing (Lens (Lens Bool)) (d := levelTwo)

/-- Level 4: HasDistinguishing (Lens (Lens (Lens (Lens Bool)))). -/
def levelFour : HasDistinguishing (Lens (Lens (Lens (Lens Bool)))) :=
  lensHasDistinguishing (Lens (Lens (Lens Bool))) (d := levelThree)

/-! ### Universal morphisms at each level -/

/-- Raw → Lens (Lens Bool) universal morphism. -/
def universalMorphismLevelTwo : Raw → Lens (Lens Bool) :=
  @universalMorphism (Lens (Lens Bool)) levelTwo

/-- Raw → Lens (Lens (Lens Bool)) universal morphism. -/
def universalMorphismLevelThree : Raw → Lens (Lens (Lens Bool)) :=
  @universalMorphism (Lens (Lens (Lens Bool))) levelThree

end E213.Lens.Compose.OnLens
