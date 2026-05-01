import E213.Math.Modulus.HasModulus

/-!
# Research.HasModulusBoundsExtra: trivial wrapping results for HasModulus

Derived results natural to `HasModulus xs` — modulus monotonicity,
fixed-N versions, etc.
-/

namespace E213.Math.Modulus.HasModulusBoundsExtra

open E213.Firmware E213.Hypervisor
open E213.Research.ABLens
open E213.Research.ArchimedeanCauchy
open E213.Research.HasModulusNS

/-- A larger N for HasModulus is also valid — modulus monotonicity. -/
theorem cauchy_at_larger_N (xs : Nat → Raw) (h : HasModulus xs)
    (m k : Nat) (hk : k ≥ 1) (M : Nat) (hM : M ≥ h.N m k)
    (i j : Nat) (hi : i ≥ M) (hj : j ≥ M) :
    orderProj m k (abLens.view (xs i)) =
    orderProj m k (abLens.view (xs j)) :=
  h.cauchy_at m k hk i j (Nat.le_trans hM hi) (Nat.le_trans hM hj)

end E213.Math.Modulus.HasModulusBoundsExtra
