import E213.Research.SemanticAtom

/-!
# Research.DistMorphism: distinguishing-framework category 의 morphism

`HasDistinguishing` instance 들 사이 의 structure-preserving
morphism α → β.  Identity + composition.

## Design note (sober)

Raw 의 자명 instance 에서 `combine x x = x` (idempotent — 같은
arg slash 부재 의 결과).  하지만 일반 instance (e.g., Nat with
+) 는 idempotent 부재 (`1 + 1 = 2 ≠ 1`).  따라서 `universalMorphism
α : Raw → α` 가 *모든* combine case 위 preserved 보장 부재 —
diagonal case 만.

이게 design 의 *feature*: `Raw` 의 fold structure 가 distinct
args 만 다룸 (axiom 4 의 직접 reflection).  일반 morphism α → β
는 ideally 모든 (x, y) preserve, 하지만 Raw 와 의 align 은
distinct case 만.

이 file 은 *abstract* DistMorphism 정의 (모든 case 보존) 와 그
identity / composition 만 — Raw 의 specific position 은 별도
axiom (RawInitiality / SemanticAtom 의 universalMorphism).
-/

namespace E213.Research.DistMorphism

open E213.Firmware E213.Hypervisor
open E213.Research.SemanticAtom

/-- **Distinguishing-framework morphism** (abstract, all cases). -/
structure DistMorphism (α β : Type) [d_α : HasDistinguishing α]
    [d_β : HasDistinguishing β] where
  toFun : α → β
  preserves_a : toFun d_α.a = d_β.a
  preserves_b : toFun d_α.b = d_β.b
  preserves_combine : ∀ x y, toFun (d_α.combine x y)
                              = d_β.combine (toFun x) (toFun y)

end E213.Research.DistMorphism

namespace E213.Research.DistMorphism

open E213.Firmware E213.Hypervisor
open E213.Research.SemanticAtom

/-- Identity distinguishing morphism. -/
def id (α : Type) [HasDistinguishing α] : DistMorphism α α where
  toFun := fun x => x
  preserves_a := rfl
  preserves_b := rfl
  preserves_combine := fun _ _ => rfl

/-- Composition of distinguishing morphisms. -/
def comp {α β γ : Type} [HasDistinguishing α] [HasDistinguishing β]
    [d_γ : HasDistinguishing γ]
    (f : DistMorphism α β) (g : DistMorphism β γ) : DistMorphism α γ where
  toFun := fun x => g.toFun (f.toFun x)
  preserves_a := by show g.toFun (f.toFun _) = _; rw [f.preserves_a, g.preserves_a]
  preserves_b := by show g.toFun (f.toFun _) = _; rw [f.preserves_b, g.preserves_b]
  preserves_combine := fun x y => by
    show g.toFun (f.toFun (HasDistinguishing.combine x y))
         = d_γ.combine (g.toFun (f.toFun x)) (g.toFun (f.toFun y))
    rw [f.preserves_combine, g.preserves_combine]

/-- Composition is associative. -/
theorem comp_assoc {α β γ δ : Type}
    [HasDistinguishing α] [HasDistinguishing β]
    [HasDistinguishing γ] [HasDistinguishing δ]
    (f : DistMorphism α β) (g : DistMorphism β γ) (h : DistMorphism γ δ) :
    comp (comp f g) h = comp f (comp g h) := rfl

/-- Identity is left-neutral for composition. -/
theorem id_comp {α β : Type} [HasDistinguishing α] [HasDistinguishing β]
    (f : DistMorphism α β) :
    comp (id α) f = f := rfl

/-- Identity is right-neutral for composition. -/
theorem comp_id {α β : Type} [HasDistinguishing α] [HasDistinguishing β]
    (f : DistMorphism α β) :
    comp f (id β) = f := rfl

end E213.Research.DistMorphism
