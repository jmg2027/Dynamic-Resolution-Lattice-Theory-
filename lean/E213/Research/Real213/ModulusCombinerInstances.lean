import E213.Research.Real213.ModulusCombiner

/-!
# Research.Real213ModulusCombinerInstances: trivial instances of ModulusCombiner

Kernel validation — π1 (project first), π2 (project second).

These are *trivial* combines that verify the kernel's well-formedness.
Actual addition / multiplication is separate work.
-/

namespace E213.Research.Real213.ModulusCombinerInstances

open E213.Firmware E213.Hypervisor
open E213.Research.HasModulusNS
open E213.Research.ABLens
open E213.Research.ArchimedeanCauchy

/-- **π1 combiner**: combine x y = x.  Trivial — y is ignored. -/
def piOneCombiner : ModulusCombiner (fun x _ => x) where
  precX := fun m k => (m, k)
  precY := fun _ _ => (0, 1)
  precX_k_pos := fun _ _ hk => hk
  precY_k_pos := fun _ _ _ => Nat.le_refl 1
  preserves := by
    intro _ _ _ _ _ _ _ hx _
    exact hx

/-- **π2 combiner**: combine x y = y.  Trivial — x is ignored. -/
def piTwoCombiner : ModulusCombiner (fun _ y => y) where
  precX := fun _ _ => (0, 1)
  precY := fun m k => (m, k)
  precX_k_pos := fun _ _ _ => Nat.le_refl 1
  precY_k_pos := fun _ _ hk => hk
  preserves := by
    intro _ _ _ _ _ _ _ _ hy
    exact hy

/-- **Constant combiner**: combine x y = c (fixed).  Trivial — both are ignored. -/
def constCombiner (c : Raw) : ModulusCombiner (fun _ _ => c) where
  precX := fun _ _ => (0, 1)
  precY := fun _ _ => (0, 1)
  precX_k_pos := fun _ _ _ => Nat.le_refl 1
  precY_k_pos := fun _ _ _ => Nat.le_refl 1
  preserves := by
    intro _ _ _ _ _ _ _ _ _
    rfl

end E213.Research.Real213.ModulusCombinerInstances
