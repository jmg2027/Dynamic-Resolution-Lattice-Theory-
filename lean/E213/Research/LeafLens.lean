import E213.Hypervisor.Lens
import E213.Research.LensFactoring
import E213.Meta.ParityLens

/-!
# Research.LeafLens: Raw 가 leaf 인지 여부를 Lens 로 관측

**Lens**: `leafLens : Lens Bool` 으로 "r 은 Raw.a 또는 Raw.b
인가?" 를 추출.  combine = const true.

이 Lens 는 refines preorder 에서 **leaves 와 parity 사이**에
위치 — leaves 보다는 거칠고 (정보 적음), parity 와는 incomparable.

## 정리

- `leafLens_view`: view r = "r 은 slash 가 아님".
- `leaves_refines_leafLens`: leaves 가 leafLens 를 refine.
-/

namespace E213.Research.LeafLens

open E213.Firmware E213.Hypervisor E213.Research.LensFactoring

/-- r 이 leaf (Raw.a 또는 Raw.b) 인가? -/
def leafLens : Lens Bool where
  base_a := false
  base_b := false
  combine _ _ := true

/-- leaves r ≥ 1 for all r : Raw. -/
private theorem leaves_ge_one : ∀ r : Raw, 1 ≤ Lens.leaves.view r := by
  intro r
  induction r using Raw.rec with
  | a => decide
  | b => decide
  | slash x y h ihx ihy =>
      have hfs : Lens.leaves.view (Raw.slash x y h)
                   = Lens.leaves.view x + Lens.leaves.view y := by
        apply Raw.fold_slash
        intro u v; exact Nat.add_comm u v
      rw [hfs]; omega

/-- leafLens.view r = decide (leaves r ≥ 2). -/
theorem leafLens_view_eq :
    ∀ r : Raw, leafLens.view r = decide (Lens.leaves.view r ≥ 2) := by
  intro r
  induction r using Raw.rec with
  | a => decide
  | b => decide
  | slash x y h ihx ihy =>
      have hfsL : leafLens.view (Raw.slash x y h) = true := by
        apply Raw.fold_slash
        intro u v; rfl
      have hfsN : Lens.leaves.view (Raw.slash x y h)
                    = Lens.leaves.view x + Lens.leaves.view y := by
        apply Raw.fold_slash
        intro u v; exact Nat.add_comm u v
      have hx := leaves_ge_one x
      have hy := leaves_ge_one y
      rw [hfsL, hfsN]
      have : Lens.leaves.view x + Lens.leaves.view y ≥ 2 := by omega
      simp [this]

/-- **Lens.leaves 는 leafLens 를 refine** (leaves count 가
    leaf/slash 여부를 결정).  factoring lemma 로. -/
theorem leaves_refines_leafLens : Lens.leaves.refines leafLens :=
  refines_of_factor Lens.leaves leafLens
    (fun n => decide (n ≥ 2)) leafLens_view_eq

end E213.Research.LeafLens

namespace E213.Research.LeafLens

open E213.Firmware E213.Hypervisor E213.Meta

/-- leafLens 는 parityLens 를 refine 하지 않음.
    Witness: Raw.a vs slash(a, slash(a,b)) — 둘 다 leaf-ness
    다르나 leafLens equates false/true... wait no.  실제:
    둘 다 slash 인 쌍으로 parity 만 다름.

    leafLens equates (Raw.slash a b) 과 slash(a, slash(a,b)):
    둘 다 slash → leafLens = true.  parity: 2 (even, false) vs
    3 (odd, true). 다름. -/
def rAB : Raw := Raw.slash Raw.a Raw.b (by decide)
def rAAB : Raw :=
  Raw.slash Raw.a (Raw.slash Raw.a Raw.b (by decide)) (by decide)

theorem leafLens_equates_slashes :
    leafLens.view rAB = leafLens.view rAAB := by decide

theorem parity_distinguishes_slashes :
    parityLens.view rAB ≠ parityLens.view rAAB := by decide

theorem leafLens_not_refines_parity :
    ¬ leafLens.refines parityLens := by
  intro h
  exact parity_distinguishes_slashes (h rAB rAAB leafLens_equates_slashes)

/-- parityLens 도 leafLens 를 refine 하지 않음.
    Witness: Raw.a (leaf, parity=true) vs slash(a, slash(a,b))
    (slash, parity=true) — 같은 parity, 다른 leafness. -/
theorem parity_equates_leaf_slash :
    parityLens.view Raw.a = parityLens.view rAAB := by decide

theorem leafLens_distinguishes_leaf_slash :
    leafLens.view Raw.a ≠ leafLens.view rAAB := by decide

theorem parityLens_not_refines_leafLens :
    ¬ parityLens.refines leafLens := by
  intro h
  exact leafLens_distinguishes_leaf_slash
    (h Raw.a rAAB parity_equates_leaf_slash)

end E213.Research.LeafLens
