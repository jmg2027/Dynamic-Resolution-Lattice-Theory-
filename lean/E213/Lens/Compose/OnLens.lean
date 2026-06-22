import E213.Lens.Foundations.SemanticAtom
import E213.Lens.Instances.Reach
import E213.Lens.EqPW

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
open E213.Lens.Foundations.SemanticAtom

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


/-- Pointwise xor combine of Lenses. -/
def lensXor (L M : Lens Bool) : Lens Bool :=
  ⟨xor L.base_a M.base_a, xor L.base_b M.base_b,
   fun x y => xor (L.combine x y) (M.combine x y)⟩

/-- Pointwise (eqPW) commutativity of `lensXor` — ∅-axiom; the residue-native
    form of `lensXor`'s symmetry (the readings distinguish the same things),
    avoiding the `funext` a Lens-`=` would pull on the combine field. -/
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

/-- `lensXor` is eqPW-congruent in both arguments — required to use
    `Lens.view_unique_eqPW` for the lensXor combine. -/
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


/-- **Lens-on-Lens**: Lens Bool itself is a HasDistinguishing instance. -/
def lensBoolHasDistinguishing : HasDistinguishing (Lens Bool) where
  a := constTrueLens
  b := constFalseLens
  distinct := const_lenses_distinct
  combine := lensXor
  same := Lens.eqPW
  same_refl := Lens.eqPW_refl
  same_symm := Lens.eqPW_symm
  same_trans := Lens.eqPW_trans
  combine_sym := lensXor_comm_eqPW
  combine_cong := lensXor_eqPW_cong


/-! ### Universal morphism Raw → Lens Bool

The sharpest self-application instance — elements of Raw map to
Lenses (= the representation unit of the framework). -/

/-- Universal morphism Raw → Lens Bool — `Raw.fold` on
    `(constTrueLens, constFalseLens, lensXor)`, definitionally equal to
    `@universalMorphism (Lens Bool) lensBoolHasDistinguishing`. -/
def lensUniversalMorphism : Raw → Lens Bool :=
  Raw.fold constTrueLens constFalseLens lensXor

theorem lensUniversalMorphism_a :
    lensUniversalMorphism Raw.a = constTrueLens := rfl

theorem lensUniversalMorphism_b :
    lensUniversalMorphism Raw.b = constFalseLens := rfl

/-- Slash image of `lensUniversalMorphism` as a pointwise Lens equality (eqPW):
    the residue-native form of the slash homomorphism, derived via
    `Lens.fold_slash_eqPW` and `lensXor_comm_eqPW` — ∅-axiom. -/
theorem lensUniversalMorphism_slash_eqPW (x y : Raw) (h : x ≠ y) :
    (lensUniversalMorphism (Raw.slash x y h)).eqPW
      (lensXor (lensUniversalMorphism x) (lensUniversalMorphism y)) := by
  unfold lensUniversalMorphism
  exact Lens.fold_slash_eqPW _ _ _ lensXor_comm_eqPW x y h


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

/-- Pointwise (eqPW) commutativity of `lensCombineGeneric` from `c`-commutativity
    — ∅-axiom (the residue-native form; a Lens-`=` would pull `funext`). -/
theorem lensCombineGeneric_comm_eqPW {α : Type} (c : α → α → α)
    (hsym : ∀ u v, c u v = c v u) (L M : Lens α) :
    (lensCombineGeneric c L M).eqPW (lensCombineGeneric c M L) := by
  refine ⟨?_, ?_, ?_⟩
  · exact hsym _ _
  · exact hsym _ _
  · intro x y; exact hsym _ _

/-- `lensCombineGeneric c` is eqPW-congruent in both arguments — required
    to use `Lens.view_unique_eqPW` for the generic-Lens combine. -/
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

/-- `lensCombineGeneric` symmetry up to a base relation `R` — the `sameLens`
    (recursive-tower) companion of `lensCombineGeneric_comm_eqPW`.  ∅-axiom:
    each `sameLens` component is `hRsym` at the corresponding base values. -/
theorem lensCombineGeneric_comm_same {α : Type} (c : α → α → α) (R : α → α → Prop)
    (hRsym : ∀ u v, R (c u v) (c v u)) (L M : Lens α) :
    (lensCombineGeneric c L M).sameLens R (lensCombineGeneric c M L) :=
  ⟨hRsym _ _, hRsym _ _, fun _ _ => hRsym _ _⟩

/-- `lensCombineGeneric` is `sameLens R`-congruent when `c` is `R`-congruent —
    the recursive-tower companion of `lensCombineGeneric_eqPW_cong`. -/
theorem lensCombineGeneric_cong_same {α : Type} (c : α → α → α) (R : α → α → Prop)
    (hRcong : ∀ a a' b b', R a a' → R b b' → R (c a b) (c a' b'))
    (L L' M M' : Lens α) (hL : L.sameLens R L') (hM : M.sameLens R M') :
    (lensCombineGeneric c L M).sameLens R (lensCombineGeneric c L' M') :=
  ⟨hRcong _ _ _ _ hL.1 hM.1, hRcong _ _ _ _ hL.2.1 hM.2.1,
   fun u v => hRcong _ _ _ _ (hL.2.2 u v) (hM.2.2 u v)⟩


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
  same := Lens.sameLens d.same
  same_refl := Lens.sameLens_refl d.same_refl
  same_symm := fun h => Lens.sameLens_symm (R := d.same) d.same_symm h
  same_trans := fun h1 h2 => Lens.sameLens_trans (R := d.same) d.same_trans h1 h2
  combine_sym := lensCombineGeneric_comm_same d.combine d.same d.combine_sym
  combine_cong := lensCombineGeneric_cong_same d.combine d.same d.combine_cong

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

/-! ### Universal morphisms at each level

These are direct `Raw.fold` definitions that bypass the DIRTY
`levelN` typeclass instances (whose `combine_sym` field requires
funext on the `Lens^n α` combine).  Definitionally equivalent to
`@universalMorphism (Lens^n α) levelN`, but ∅-axiom. -/

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
