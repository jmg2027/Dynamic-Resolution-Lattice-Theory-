import E213.Math.Real213.Core
import E213.Math.Modulus.HasModulus

/-!
# Research.Real213ModulusCombiner: Generic kernel for combining HasModulus

User suggestion (2026-04-26): Like the meta-algorithm pattern of EulerGenericPure,
abstract the *kernel* of modulus combination — isolating Cauchy bookkeeping
in *one place*.

`ModulusCombiner combine` = precision translation + preservation data
for combine : Raw → Raw → Raw.

`combineModulus` : two HasModulus + ModulusCombiner → combined HasModulus.
All Cauchy bookkeeping is isolated in this one theorem.

Per-operation (add, mul, ...) supplies only a ModulusCombiner instance.
-/

namespace E213.Math.Real213.ModulusCombiner

open E213.Firmware E213.Hypervisor
open E213.Math.Modulus.HasModulus
open E213.Hypervisor.Lens.Instances.AB
open E213.Math.Cauchy.Archimedean
open E213.Math.Real213.Core (Real213)

/-- **ModulusCombiner**: abstract kernel for sequence combine + Cauchy preservation. -/
structure ModulusCombiner (combine : Raw → Raw → Raw) where
  precX : Nat → Nat → Nat × Nat
  precY : Nat → Nat → Nat × Nat
  precX_k_pos : ∀ m k, k ≥ 1 → (precX m k).2 ≥ 1
  precY_k_pos : ∀ m k, k ≥ 1 → (precY m k).2 ≥ 1
  preserves : ∀ (m k : Nat), k ≥ 1 →
    ∀ (x1 x2 y1 y2 : Raw),
      orderProj (precX m k).1 (precX m k).2 (abLens.view x1)
        = orderProj (precX m k).1 (precX m k).2 (abLens.view x2) →
      orderProj (precY m k).1 (precY m k).2 (abLens.view y1)
        = orderProj (precY m k).1 (precY m k).2 (abLens.view y2) →
      orderProj m k (abLens.view (combine x1 y1))
        = orderProj m k (abLens.view (combine x2 y2))

end E213.Math.Real213.ModulusCombiner

namespace E213.Math.Real213.ModulusCombiner

open E213.Firmware E213.Hypervisor
open E213.Math.Modulus.HasModulus
open E213.Hypervisor.Lens.Instances.AB
open E213.Math.Cauchy.Archimedean
open E213.Math.Real213.Core (Real213)

/-- **Generic combine theorem**: ModulusCombiner + two HasModulus → combined HasModulus. -/
def combineModulus {xs ys : Nat → Raw}
    (mod_x : HasModulus xs) (mod_y : HasModulus ys)
    {combine : Raw → Raw → Raw}
    (mc : ModulusCombiner combine) :
    HasModulus (fun n => combine (xs n) (ys n)) where
  N := fun m k =>
    max (mod_x.N (mc.precX m k).1 (mc.precX m k).2)
        (mod_y.N (mc.precY m k).1 (mc.precY m k).2)
  cauchy_at := by
    intro m k hk i j hi hj
    show orderProj m k (abLens.view (combine (xs i) (ys i)))
       = orderProj m k (abLens.view (combine (xs j) (ys j)))
    have hi_x : i ≥ mod_x.N (mc.precX m k).1 (mc.precX m k).2 :=
      Nat.le_trans (Nat.le_max_left _ _) hi
    have hi_y : i ≥ mod_y.N (mc.precY m k).1 (mc.precY m k).2 :=
      Nat.le_trans (Nat.le_max_right _ _) hi
    have hj_x : j ≥ mod_x.N (mc.precX m k).1 (mc.precX m k).2 :=
      Nat.le_trans (Nat.le_max_left _ _) hj
    have hj_y : j ≥ mod_y.N (mc.precY m k).1 (mc.precY m k).2 :=
      Nat.le_trans (Nat.le_max_right _ _) hj
    have hx := mod_x.cauchy_at (mc.precX m k).1 (mc.precX m k).2
                 (mc.precX_k_pos m k hk) i j hi_x hj_x
    have hy := mod_y.cauchy_at (mc.precY m k).1 (mc.precY m k).2
                 (mc.precY_k_pos m k hk) i j hi_y hj_y
    exact mc.preserves m k hk (xs i) (xs j) (ys i) (ys j) hx hy

end E213.Math.Real213.ModulusCombiner
