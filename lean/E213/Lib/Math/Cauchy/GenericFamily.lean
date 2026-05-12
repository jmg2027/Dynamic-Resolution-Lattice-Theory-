import E213.Lens.Instances.Cauchy
import E213.Lens.Instances.AB
import E213.Lib.Math.Cauchy.Archimedean
import E213.Lib.Math.Cauchy.ProfiniteSeq
import E213.Lib.Math.NatHelpers.AddMod213

/-!
# GenericFamilyCauchy: Unified framework for Lens + post-processing

Explicitly identifies ArchimedeanCauchy (orderProj family) and
ProfiniteSeq (mod m family) as **two instances of the same abstraction**.

## Unified form

`(L, F) family-Cauchy` where L : Lens α, F : ι → α → β:

```
∀ i, ∃ N, ∀ k l ≥ N, F i (L.view (xs k)) = F i (L.view (xs l))
```

ι, β are arbitrary types.

- **Profinite case**: L = Lens.leaves, F m = (· % m), β = Nat.
- **Archimedean case**: L = abLens, F (m, k) = orderProj m k,
  β = Bool.

## Significance

Mingu (c)+(d): "Profinite ↔ Archimedean are both differences in Lens
family choice.  Same limitLens mechanism."

This file is the formal expression of that unification.
-/

namespace E213.Lib.Math.Cauchy.GenericFamily

open E213.Theory E213.Lens

/-- **Generic family-Cauchy**: Cauchy condition for a family of derived
    projections F over the view of Lens L. -/
def GFCauchy {α β : Type} {ι : Type} (L : Lens α) (F : ι → α → β)
    (xs : Nat → Raw) : Prop :=
  ∀ i, ∃ N, ∀ k l, k ≥ N → l ≥ N →
    F i (L.view (xs k)) = F i (L.view (xs l))

/-- **Generic Cauchy data**: explicit witness + post-processing. -/
structure GFCauchyData {α β : Type} {ι : Type}
    (L : Lens α) (F : ι → α → β) (xs : Nat → Raw) where
  N : ι → Nat
  cauchy : ∀ i k l, k ≥ N i → l ≥ N i →
    F i (L.view (xs k)) = F i (L.view (xs l))

/-- Extract limit assignment. -/
def GFCauchyData.limitAssign {α β : Type} {ι : Type}
    {L : Lens α} {F : ι → α → β} {xs : Nat → Raw}
    (cd : GFCauchyData L F xs) : ι → β :=
  fun i => F i (L.view (xs (cd.N i)))

/-- Well-definedness of limit assignment. -/
theorem limitAssign_eq_tail {α β : Type} {ι : Type}
    {L : Lens α} {F : ι → α → β} {xs : Nat → Raw}
    (cd : GFCauchyData L F xs) (i : ι) (n : Nat) (hn : n ≥ cd.N i) :
    F i (L.view (xs n)) = cd.limitAssign i :=
  cd.cauchy i n (cd.N i) hn (Nat.le_refl _)

end E213.Lib.Math.Cauchy.GenericFamily

namespace E213.Lib.Math.Cauchy.GenericFamily

open E213.Theory E213.Lens
open E213.Lens.Instances.Cauchy

/-- **LensCauchy is GFCauchy instance** with trivial family
    (single Lens, identity post-processing). -/
theorem lensCauchy_is_GFCauchy {α : Type} (L : Lens α)
    (xs : Nat → Raw) (h : LensCauchy L xs) :
    GFCauchy L (fun (_ : Unit) (a : α) => a) xs := by
  intro _
  obtain ⟨N, hN⟩ := h
  refine ⟨N, ?_⟩
  intro k l hk hl
  exact hN k l hk hl

end E213.Lib.Math.Cauchy.GenericFamily

namespace E213.Lib.Math.Cauchy.GenericFamily

open E213.Theory E213.Lens

/-- **ArchimedeanCauchy is GFCauchy instance**: orderProj family +
    abLens is GFCauchy with ι = Nat × Nat, β = Bool. -/
theorem orderCauchy_is_GFCauchy
    (xs : Nat → Raw)
    (h : E213.Lib.Math.Cauchy.Archimedean.isOrderCauchy xs) :
    GFCauchy E213.Lens.Instances.AB.abLens
      (fun (mk : Nat × Nat) (p : Nat × Nat) =>
         E213.Lib.Math.Cauchy.Archimedean.orderProj mk.1 mk.2 p) xs := by
  intro mk
  match (inferInstance : Decidable (mk.2 ≥ 1)) with
  | .isTrue hk =>
    obtain ⟨N, hN⟩ := h mk.1 mk.2 hk
    exact ⟨N, hN⟩
  | .isFalse hk =>
    -- mk.2 = 0: orderProj is always true (since p.1 * 0 = 0 ≤ p.2 * mk.1)
    refine ⟨0, ?_⟩
    intro k l _ _
    show E213.Lib.Math.Cauchy.Archimedean.orderProj mk.1 mk.2 _ =
         E213.Lib.Math.Cauchy.Archimedean.orderProj mk.1 mk.2 _
    have hk0 : mk.2 = 0 := by
      match hmk2 : mk.2 with
      | 0 => rfl
      | n + 1 =>
        exfalso
        apply hk
        rw [hmk2]
        exact Nat.succ_le_succ (Nat.zero_le n)
    unfold E213.Lib.Math.Cauchy.Archimedean.orderProj
    rw [hk0, Nat.mul_zero, Nat.mul_zero]
    rw [decide_eq_true (Nat.zero_le _), decide_eq_true (Nat.zero_le _)]

end E213.Lib.Math.Cauchy.GenericFamily

namespace E213.Lib.Math.Cauchy.GenericFamily

open E213.Theory E213.Lens

/-- **Profinite (factorial) Cauchy is GFCauchy instance**:
    Lens.leaves + (· % (m+1)) family.  Index is ℕ with m+1 ensuring
    m+1 ≥ 1 automatically. -/
theorem profinite_factorial_is_GFCauchy
    (xs : Nat → Raw)
    (hLeaves : ∀ n, Lens.leaves.view (xs n)
                 = E213.Lib.Math.Cauchy.ProfiniteSeq.factorial (n + 1)) :
    GFCauchy Lens.leaves (fun (m : Nat) (n : Nat) => n % (m + 1)) xs := by
  intro m
  refine ⟨m + 1, ?_⟩
  intro k l hk hl
  show Lens.leaves.view (xs k) % (m + 1) = Lens.leaves.view (xs l) % (m + 1)
  rw [hLeaves k, hLeaves l]
  have hmp : 1 ≤ m + 1 := Nat.succ_le_succ (Nat.zero_le m)
  rw [E213.Lib.Math.Cauchy.ProfiniteSeq.factorial_eventually_zero_mod
        (m+1) hmp k (Nat.le_succ_of_le hk),
      E213.Lib.Math.Cauchy.ProfiniteSeq.factorial_eventually_zero_mod
        (m+1) hmp l (Nat.le_succ_of_le hl)]

end E213.Lib.Math.Cauchy.GenericFamily

namespace E213.Lib.Math.Cauchy.GenericFamily

open E213.Theory E213.Lens

/-- **ProjectionLens**: when F is fold-compatible, constructs a
    single Lens (ι → β). -/
def projectionLens {α β ι : Type} (L : Lens α) (F : ι → α → β)
    (combine_β : ι → β → β → β) :
    Lens (ι → β) where
  base_a := fun i => F i L.base_a
  base_b := fun i => F i L.base_b
  combine f g := fun i => combine_β i (f i) (g i)

/-- ProjectionLens view is pointwise (assuming fold-compatibility). -/
theorem projectionLens_view {α β ι : Type} (L : Lens α) (F : ι → α → β)
    (combine_β : ι → β → β → β)
    (hLsym : ∀ u v, L.combine u v = L.combine v u)
    (hβsym : ∀ i u v, combine_β i u v = combine_β i v u)
    (compat : ∀ i u v, F i (L.combine u v) = combine_β i (F i u) (F i v))
    (r : Raw) :
    (projectionLens L F combine_β).view r = fun i => F i (L.view r) := by
  induction r using Raw.rec with
  | a => rfl
  | b => rfl
  | slash x y h ihx ihy =>
      have hLproj_sym : ∀ u v : ι → β,
          (projectionLens L F combine_β).combine u v
            = (projectionLens L F combine_β).combine v u := by
        intro u v; funext i
        exact hβsym i (u i) (v i)
      have hfsP : (projectionLens L F combine_β).view (Raw.slash x y h)
                    = (projectionLens L F combine_β).combine
                        ((projectionLens L F combine_β).view x)
                        ((projectionLens L F combine_β).view y) := by
        apply Raw.fold_slash _ _ _ hLproj_sym
      have hfsL : L.view (Raw.slash x y h)
                    = L.combine (L.view x) (L.view y) := by
        apply Raw.fold_slash _ _ _ hLsym
      rw [hfsP, ihx, ihy]
      funext i
      show combine_β i (F i (L.view x)) (F i (L.view y))
           = F i (L.view (Raw.slash x y h))
      rw [hfsL]
      exact (compat i (L.view x) (L.view y)).symm

end E213.Lib.Math.Cauchy.GenericFamily

namespace E213.Lib.Math.Cauchy.GenericFamily

open E213.Theory E213.Lens

/-- **Mod family projectionLens**: leaves + mod are fold-compatible,
    giving a single fold-structured Lens (Nat → Nat). -/
def leavesModAllLens : Lens (Nat → Nat) :=
  projectionLens Lens.leaves
    (fun (m : Nat) (n : Nat) => n % (m + 1))
    (fun (m : Nat) (a b : Nat) => (a + b) % (m + 1))

/-- The m-th component of leavesModAllLens.view r = leaves r % (m+1).
    PURE — uses `AddMod213.add_mod_gen` (∅-axiom) in place of
    Lean-core `Nat.add_mod` (propext-leaking). -/
theorem leavesModAllLens_view (r : Raw) :
    leavesModAllLens.view r = fun m => Lens.leaves.view r % (m + 1) := by
  apply projectionLens_view
  · intro u v; exact Nat.add_comm u v
  · intro _ u v; rw [Nat.add_comm u v]
  · intro m u v
    exact E213.Lib.Math.NatHelpers.AddMod213.add_mod_gen u v (m + 1)

end E213.Lib.Math.Cauchy.GenericFamily
