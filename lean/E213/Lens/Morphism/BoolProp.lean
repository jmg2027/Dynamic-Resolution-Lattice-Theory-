import E213.Lens.SemanticAtom
import E213.Lens.Instances.Reach

/-!
# BoolHasDistinguishing instances (xor / or / iff combines)

`HasDistinguishing Bool` instances for the three connectives that are
both commutative and definable on `Bool`.  Used by the universal
morphism construction of various Lens-on-Bool examples.

The Bool↔Prop bridge previously in this file was deleted: it
required `propext` to express Prop equality, in violation of the
"design-by-funext/propext 금지" directive.  Bool versions only.
-/

namespace E213.Lens.Morphism.BoolProp

open E213.Theory E213.Lens
open E213.Lens.SemanticAtom
open E213.Lens.Instances.Reach

/-- Bool with xor combine instance. -/
def boolXorHasDistinguishing : HasDistinguishing Bool where
  a := true
  b := false
  distinct := by decide
  combine := xor
  combine_sym := by intros x y; cases x <;> cases y <;> rfl

/-- Bool with or combine instance. -/
def boolOrHasDistinguishing : HasDistinguishing Bool where
  a := true
  b := false
  distinct := by decide
  combine := Bool.or
  combine_sym := Bool.or_comm

/-- Bool with beq (= equality on Bool) combine instance. -/
def boolIffHasDistinguishing : HasDistinguishing Bool where
  a := true
  b := false
  distinct := by decide
  combine := fun x y => decide (x = y)
  combine_sym := by intros x y; cases x <;> cases y <;> rfl

end E213.Lens.Morphism.BoolProp
