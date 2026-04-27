import E213.Hypervisor.Lens
import E213.Research.LensFactoring

/-!
# Research.ABLens: Raw.a 수, Raw.b 수 를 따로 카운트

`abLens : Lens (Nat × Nat)` — view r = (r 의 Raw.a leaf 수,
r 의 Raw.b leaf 수).

## 위상

Refines preorder 에서 Lens.leaves 보다 finer (Raw.a 와
Raw.b 를 구별).  boolXorLens 보다도 finer (a-count 의
full value vs mod 2).

- `abLens_refines_leaves` : Lens.leaves 의 총합 정보 포함.
- abLens 의 kernel: `(a count, b count)` 가 같은 Raw 들.

이는 note 41 Q41.3 ("refines preorder 의 각 level 의 kernel
개수") 의 구체 layer 하나.
-/

namespace E213.Research.ABLens

open E213.Firmware E213.Hypervisor E213.Research.LensFactoring

/-- Raw.a count와 Raw.b count 를 componentwise 로 track. -/
def abLens : Lens (Nat × Nat) where
  base_a := (1, 0)
  base_b := (0, 1)
  combine p q := (p.1 + q.1, p.2 + q.2)

private theorem abLens_sym (u v : Nat × Nat) :
    abLens.combine u v = abLens.combine v u := by
  show (u.1 + v.1, u.2 + v.2) = (v.1 + u.1, v.2 + u.2)
  rw [Nat.add_comm u.1 v.1, Nat.add_comm u.2 v.2]

/-- view 의 두 성분을 합하면 leaves count. -/
theorem abLens_sum_eq_leaves :
    ∀ r : Raw, (abLens.view r).1 + (abLens.view r).2 = Lens.leaves.view r := by
  intro r
  induction r using Raw.rec with
  | a => rfl
  | b => rfl
  | slash x y h ihx ihy =>
      have hfsA : abLens.view (Raw.slash x y h)
                    = abLens.combine (abLens.view x) (abLens.view y) :=
        Raw.fold_slash _ _ _ abLens_sym x y h
      have hfsL : Lens.leaves.view (Raw.slash x y h)
                    = Lens.leaves.view x + Lens.leaves.view y := by
        apply Raw.fold_slash
        intro u v; exact Nat.add_comm u v
      rw [hfsA, hfsL]
      show (abLens.view x).1 + (abLens.view y).1
           + ((abLens.view x).2 + (abLens.view y).2)
           = Lens.leaves.view x + Lens.leaves.view y
      omega

/-- Factor function sum: (a, b) ↦ a + b. -/
private def sumFactor (p : Nat × Nat) : Nat := p.1 + p.2

/-- **abLens refines leaves**. -/
theorem abLens_refines_leaves : abLens.refines Lens.leaves := by
  apply refines_of_factor abLens Lens.leaves sumFactor
  intro r
  exact (abLens_sum_eq_leaves r).symm

end E213.Research.ABLens

namespace E213.Research.ABLens

open E213.Firmware E213.Hypervisor

/-- Witness: 2a + 1b. -/
def rAAB : Raw :=
  Raw.slash Raw.a (Raw.slash Raw.a Raw.b (by decide)) (by decide)

/-- Witness: 1a + 2b. -/
def rABB : Raw :=
  Raw.slash Raw.b (Raw.slash Raw.a Raw.b (by decide)) (by decide)

theorem leaves_equates : Lens.leaves.view rAAB = Lens.leaves.view rABB := by decide

theorem abLens_distinguishes :
    abLens.view rAAB ≠ abLens.view rABB := by decide

/-- **abLens ⊏ Lens.leaves** 엄격 (같은 leaves 수, 다른 (a, b) 분포). -/
theorem leaves_not_refines_abLens : ¬ Lens.leaves.refines abLens := by
  intro h
  exact abLens_distinguishes (h rAAB rABB leaves_equates)

end E213.Research.ABLens
