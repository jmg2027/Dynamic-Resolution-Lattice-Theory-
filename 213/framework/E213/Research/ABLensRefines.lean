import E213.Research.ABLens
import E213.Research.LeavesRefinesParity
import E213.Meta.BoolLens

/-!
# Research.ABLensRefines: abLens ⊏ parityLens, abLens ⊏ boolXorLens

abLens (a-count, b-count) 은 parityLens (total parity) 와
boolXorLens (a-count parity) 를 모두 refine.  Transitively,
abLens 는 leaves 도 refine (ABLens.lean 의 abLens_refines_leaves).

## 정리

- `abLens_refines_parityLens`: abLens ⊏ parityLens.
- `abLens_refines_boolXorLens`: abLens ⊏ boolXorLens.

## 의의

abLens 가 refines preorder 에서 세 Bool kernel 을 동시에 refine:
- leaves (via sum factor).
- parityLens (via sum parity factor).
- boolXorLens (via a parity factor).

Raw 의 basic 정보 추출 (a-count, b-count) 이 여러 "derived"
관측을 모두 포함.
-/

namespace E213.Research.ABLensRefines

open E213.Firmware E213.Hypervisor E213.Meta
open E213.Research.ABLens E213.Research.LensFactoring

/-- Factor function: (a, b) ↦ parity of sum. -/
private def sumParityFactor (p : Nat × Nat) : Bool :=
  decide ((p.1 + p.2) % 2 = 1)

/-- **abLens refines parityLens**. -/
theorem abLens_refines_parityLens : abLens.refines parityLens := by
  apply refines_of_factor abLens parityLens sumParityFactor
  intro r
  rw [E213.Research.LeavesRefinesParity.parityLens_view_eq_leaves_odd]
  show decide (Lens.leaves.view r % 2 = 1)
       = decide (((abLens.view r).1 + (abLens.view r).2) % 2 = 1)
  rw [abLens_sum_eq_leaves]

end E213.Research.ABLensRefines

namespace E213.Research.ABLensRefines

open E213.Firmware E213.Hypervisor E213.Meta
open E213.Research.ABLens E213.Research.LensFactoring

/-- Factor function: (a, b) ↦ parity of a. -/
private def aParityFactor (p : Nat × Nat) : Bool :=
  decide (p.1 % 2 = 1)

/-- boolXorLens view 는 a-count mod 2.  (Note 37 catalogue 와
    일관.)  Raw.rec induction 으로 직접. -/
private theorem boolXorLens_view_eq (r : Raw) :
    boolXorLens.view r = decide ((abLens.view r).1 % 2 = 1) := by
  induction r using Raw.rec with
  | a => decide
  | b => decide
  | slash x y h ihx ihy =>
      have hfsB : boolXorLens.view (Raw.slash x y h)
                    = xor (boolXorLens.view x) (boolXorLens.view y) := by
        apply Raw.fold_slash
        intro u v; cases u <;> cases v <;> rfl
      have hfsA : abLens.view (Raw.slash x y h)
                    = ((abLens.view x).1 + (abLens.view y).1,
                       (abLens.view x).2 + (abLens.view y).2) := by
        apply Raw.fold_slash
        intro u v
        show (u.1 + v.1, u.2 + v.2) = (v.1 + u.1, v.2 + u.2)
        rw [Nat.add_comm u.1 v.1, Nat.add_comm u.2 v.2]
      rw [hfsB, hfsA, ihx, ihy]
      rcases Nat.mod_two_eq_zero_or_one (abLens.view x).1 with ha | ha
      all_goals rcases Nat.mod_two_eq_zero_or_one (abLens.view y).1 with hb | hb
      all_goals simp_all [Nat.add_mod]

/-- **abLens refines boolXorLens**. -/
theorem abLens_refines_boolXorLens : abLens.refines boolXorLens := by
  apply refines_of_factor abLens boolXorLens aParityFactor
  intro r
  exact boolXorLens_view_eq r

end E213.Research.ABLensRefines
