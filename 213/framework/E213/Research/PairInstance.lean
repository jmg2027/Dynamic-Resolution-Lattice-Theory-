import E213.Research.SemanticAtom
import E213.Research.InstanceReach

/-!
# Research.PairInstance: categorical product of HasDistinguishing

`α × β` 가 HasDistinguishing instance — 두 instance 의 categorical
product.  universalMorphism 이 components 별 fold 로 split.

## 결과

- `pairHasDistinguishing α β`: pair instance.
- `universalMorphism_pair_commute`: universalMorphism (α × β)
  = (universalMorphism α, universalMorphism β) componentwise.

이게 distinguishing-framework category 의 *binary product* 의
universal property — 의미 atom 의 product structure.
-/

namespace E213.Research.PairInstance

open E213.Firmware E213.Hypervisor
open E213.Research.SemanticAtom

/-- Pair instance: 두 HasDistinguishing 의 product. -/
def pairHasDistinguishing (α β : Type) [d_α : HasDistinguishing α]
    [d_β : HasDistinguishing β] : HasDistinguishing (α × β) where
  a := (d_α.a, d_β.a)
  b := (d_α.b, d_β.b)
  distinct := fun h => d_α.distinct (congrArg Prod.fst h)
  combine := fun p q => (d_α.combine p.1 q.1, d_β.combine p.2 q.2)
  combine_sym := by
    intro p q
    show (d_α.combine p.1 q.1, d_β.combine p.2 q.2)
         = (d_α.combine q.1 p.1, d_β.combine q.2 p.2)
    rw [d_α.combine_sym, d_β.combine_sym]

end E213.Research.PairInstance

namespace E213.Research.PairInstance

open E213.Firmware E213.Hypervisor
open E213.Research.SemanticAtom

/-- **Universal property of binary product**: universalMorphism (α × β)
    가 components 별 universalMorphism 의 pair. -/
theorem universalMorphism_pair_commute (α β : Type)
    [d_α : HasDistinguishing α] [d_β : HasDistinguishing β] (r : Raw) :
    @universalMorphism (α × β) (pairHasDistinguishing α β) r
      = (universalMorphism α r, universalMorphism β r) := by
  induction r using Raw.rec with
  | a =>
      have h_pair : @universalMorphism (α × β) (pairHasDistinguishing α β) Raw.a
                    = (d_α.a, d_β.a) :=
        @universalMorphism_a (α × β) (pairHasDistinguishing α β)
      have h_α : universalMorphism α Raw.a = d_α.a := universalMorphism_a α
      have h_β : universalMorphism β Raw.a = d_β.a := universalMorphism_a β
      rw [h_pair, h_α, h_β]
  | b =>
      have h_pair : @universalMorphism (α × β) (pairHasDistinguishing α β) Raw.b
                    = (d_α.b, d_β.b) :=
        @universalMorphism_b (α × β) (pairHasDistinguishing α β)
      have h_α : universalMorphism α Raw.b = d_α.b := universalMorphism_b α
      have h_β : universalMorphism β Raw.b = d_β.b := universalMorphism_b β
      rw [h_pair, h_α, h_β]
  | slash x y h ihx ihy =>
      have h_pair : @universalMorphism (α × β) (pairHasDistinguishing α β)
                      (Raw.slash x y h)
                  = (pairHasDistinguishing α β).combine
                      (@universalMorphism (α × β) (pairHasDistinguishing α β) x)
                      (@universalMorphism (α × β) (pairHasDistinguishing α β) y) :=
        @universalMorphism_slash (α × β) (pairHasDistinguishing α β) x y h
      have h_α : universalMorphism α (Raw.slash x y h)
                  = d_α.combine (universalMorphism α x) (universalMorphism α y) :=
        universalMorphism_slash α x y h
      have h_β : universalMorphism β (Raw.slash x y h)
                  = d_β.combine (universalMorphism β x) (universalMorphism β y) :=
        universalMorphism_slash β x y h
      rw [h_pair, h_α, h_β, ihx, ihy]
      rfl

end E213.Research.PairInstance

namespace E213.Research.PairInstance

open E213.Firmware E213.Hypervisor
open E213.Research.SemanticAtom

/-! ### Pair forget projections (categorical projection morphisms)

`α × β → α` 와 `α × β → β` 가 distinguishing-framework category
의 *projection* — categorical product 의 universal property 의
일부.

`DistMorphism` 의 typeclass synthesis 부재 라 직접 record 형식.
-/

/-- pair forget projection α × β → α 의 properties. -/
theorem pair_forget_first_a (α β : Type)
    [d_α : HasDistinguishing α] [d_β : HasDistinguishing β] :
    Prod.fst (pairHasDistinguishing α β).a = d_α.a := rfl

theorem pair_forget_first_b (α β : Type)
    [d_α : HasDistinguishing α] [d_β : HasDistinguishing β] :
    Prod.fst (pairHasDistinguishing α β).b = d_α.b := rfl

theorem pair_forget_first_combine (α β : Type)
    [d_α : HasDistinguishing α] [d_β : HasDistinguishing β] (p q : α × β) :
    Prod.fst ((pairHasDistinguishing α β).combine p q)
      = d_α.combine (Prod.fst p) (Prod.fst q) := rfl

theorem pair_forget_second_a (α β : Type)
    [d_α : HasDistinguishing α] [d_β : HasDistinguishing β] :
    Prod.snd (pairHasDistinguishing α β).a = d_β.a := rfl

theorem pair_forget_second_b (α β : Type)
    [d_α : HasDistinguishing α] [d_β : HasDistinguishing β] :
    Prod.snd (pairHasDistinguishing α β).b = d_β.b := rfl

theorem pair_forget_second_combine (α β : Type)
    [d_α : HasDistinguishing α] [d_β : HasDistinguishing β] (p q : α × β) :
    Prod.snd ((pairHasDistinguishing α β).combine p q)
      = d_β.combine (Prod.snd p) (Prod.snd q) := rfl

end E213.Research.PairInstance

namespace E213.Research.PairInstance

open E213.Firmware E213.Hypervisor
open E213.Research.SemanticAtom

/-! ### Universal property 와 forget 의 결합

universalMorphism (α × β) 의 first/second projection 이 components
별 universalMorphism — categorical product 의 universal property
의 직접 귀결. -/

theorem universalMorphism_first (α β : Type)
    [d_α : HasDistinguishing α] [d_β : HasDistinguishing β] (r : Raw) :
    Prod.fst (@universalMorphism (α × β) (pairHasDistinguishing α β) r)
      = universalMorphism α r := by
  rw [universalMorphism_pair_commute]

theorem universalMorphism_second (α β : Type)
    [d_α : HasDistinguishing α] [d_β : HasDistinguishing β] (r : Raw) :
    Prod.snd (@universalMorphism (α × β) (pairHasDistinguishing α β) r)
      = universalMorphism β r := by
  rw [universalMorphism_pair_commute]

end E213.Research.PairInstance
