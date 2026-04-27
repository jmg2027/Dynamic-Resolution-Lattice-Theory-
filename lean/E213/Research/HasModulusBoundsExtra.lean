import E213.Research.HasModulus

/-!
# Research.HasModulusBoundsExtra: HasModulus 의 trivial wrapping
results

`HasModulus xs` 와 함께 자연 한 derived results — modulus
의 monotonicity, fixed-N versions, etc.
-/

namespace E213.Research.HasModulusBoundsExtra

open E213.Firmware E213.Hypervisor
open E213.Research.ABLens
open E213.Research.ArchimedeanCauchy
open E213.Research.HasModulusNS

/-- HasModulus 의 N 을 더 크 게 잡 아 도 OK — modulus 의
    monotonicity. -/
theorem cauchy_at_larger_N (xs : Nat → Raw) (h : HasModulus xs)
    (m k : Nat) (hk : k ≥ 1) (M : Nat) (hM : M ≥ h.N m k)
    (i j : Nat) (hi : i ≥ M) (hj : j ≥ M) :
    orderProj m k (abLens.view (xs i)) =
    orderProj m k (abLens.view (xs j)) :=
  h.cauchy_at m k hk i j (Nat.le_trans hM hi) (Nat.le_trans hM hj)

end E213.Research.HasModulusBoundsExtra
