import E213.Hypervisor.Lens
import E213.Research.LensFactoring

/-!
# Research.LeavesModNat: leaves mod m 의 divisibility → refinement

mod m 계열 Lens 의 통합 form.  임의의 m ≥ 2 에 대해 Lens Nat
으로 leaves mod m 관측.

**핵심**: `k ∣ m → leavesModNat m refines leavesModNat k`.  즉
mod m family 는 divisibility lattice 와 동형 (refines preorder
의 반영).

note 41 §4 의 countable 무한 하한의 구체 구조.
-/

namespace E213.Research.LeavesModNat

open E213.Firmware E213.Hypervisor E213.Research.LensFactoring

/-- Leaves mod m Lens (m ≥ 2).  view r = leaves r % m. -/
def leavesModNat (m : Nat) : Lens Nat where
  base_a := 1 % m
  base_b := 1 % m
  combine u v := (u + v) % m

private theorem mod_add_comm (m a b : Nat) :
    (a + b) % m = (b + a) % m := by rw [Nat.add_comm]

/-- leavesModNat m 의 view = leaves r % m. -/
theorem leavesModNat_view_eq (m : Nat) :
    ∀ r : Raw, (leavesModNat m).view r = Lens.leaves.view r % m := by
  intro r
  induction r using Raw.rec with
  | a => rfl
  | b => rfl
  | slash x y h ihx ihy =>
      have hfsM : (leavesModNat m).view (Raw.slash x y h)
                    = (leavesModNat m).combine
                        ((leavesModNat m).view x) ((leavesModNat m).view y) :=
        Raw.fold_slash _ _ _ (mod_add_comm m) x y h
      have hfsL : Lens.leaves.view (Raw.slash x y h)
                    = Lens.leaves.view x + Lens.leaves.view y := by
        apply Raw.fold_slash
        intro u v; exact Nat.add_comm u v
      rw [hfsM, hfsL]
      show (((leavesModNat m).view x) + ((leavesModNat m).view y)) % m
           = (Lens.leaves.view x + Lens.leaves.view y) % m
      rw [ihx, ihy]
      exact Nat.add_mod _ _ m |>.symm

end E213.Research.LeavesModNat

namespace E213.Research.LeavesModNat

open E213.Firmware E213.Hypervisor E213.Research.LensFactoring

/-- divisibility → refinement: k ∣ m ⟹ mod m refines mod k. -/
theorem divides_refines (m k : Nat) (hmk : k ∣ m) :
    (leavesModNat m).refines (leavesModNat k) := by
  apply refines_of_factor (leavesModNat m) (leavesModNat k)
    (fun n => n % k)
  intro r
  rw [leavesModNat_view_eq m, leavesModNat_view_eq k]
  obtain ⟨q, hq⟩ := hmk
  have : Lens.leaves.view r % m % k = Lens.leaves.view r % k := by
    rw [hq]
    exact Nat.mod_mod_of_dvd _ ⟨q, rfl⟩
  exact this.symm

end E213.Research.LeavesModNat
