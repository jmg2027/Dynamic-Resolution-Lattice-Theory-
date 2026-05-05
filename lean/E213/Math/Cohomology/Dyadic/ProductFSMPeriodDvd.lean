import E213.Math.Cohomology.Dyadic.ProductFSMRun
import E213.Math.Cohomology.Dyadic.LCMClosure

import E213.Math.Cohomology.Dyadic.BitFSM
import E213.Math.Cohomology.Dyadic.ProductFSM
/-!
# Lens Composition (∅-axiom variant) — explicit `L` with dvd witnesses

`lens_composition_period` invokes `Nat.dvd_lcm_left/right` which leak
`propext`.  This variant takes the common period `L` together with
explicit divisibility witnesses `p ∣ L`, `q ∣ L`, supplied by `decide`
in concrete callers.  Result is fully ∅-axiom.
-/

namespace E213.Math.Cohomology.Dyadic.ProductFSMPeriodDvd

open E213.Math.Cohomology.Dyadic.BitFSM (BitFSM)
open E213.Math.Cohomology.Dyadic.ProductFSM
open E213.Math.Cohomology.Dyadic.ProductFSMRun (product_bits_eq)
open E213.Math.Cohomology.Dyadic.LCMClosure (bs_periodic_of_dvd)

/-- Lens composition with explicit common period `L` + dvd witnesses.
    ∅-axiom — tactic-free to avoid `rw`-induced propext leak. -/
theorem lens_composition_period_dvd {n m : Nat} (hm : 0 < m)
    (f1 : BitFSM n) (f2 : BitFSM m) (g : Bool → Bool → Bool)
    (p q L : Nat) (hp : 0 < p) (hq : 0 < q)
    (hpL : p ∣ L) (hqL : q ∣ L)
    (h1 : ∀ k, f1.bits (k + p) = f1.bits k)
    (h2 : ∀ k, f2.bits (k + q) = f2.bits k) :
    ∀ k, (BitFSM.product hm f1 f2 g).bits (k + L)
        = (BitFSM.product hm f1 f2 g).bits k := fun k =>
  let h1L : f1.bits (k + L) = f1.bits k :=
    bs_periodic_of_dvd f1.bits p L hp hpL h1 k
  let h2L : f2.bits (k + L) = f2.bits k :=
    bs_periodic_of_dvd f2.bits q L hq hqL h2 k
  let step1 : (BitFSM.product hm f1 f2 g).bits (k + L)
              = g (f1.bits (k + L)) (f2.bits (k + L)) :=
    product_bits_eq hm f1 f2 g (k + L)
  let step2 : (BitFSM.product hm f1 f2 g).bits k
              = g (f1.bits k) (f2.bits k) :=
    product_bits_eq hm f1 f2 g k
  let step3 : g (f1.bits (k + L)) (f2.bits (k + L))
              = g (f1.bits k) (f2.bits k) :=
    h1L ▸ h2L ▸ rfl
  step1.trans (step3.trans step2.symm)

end E213.Math.Cohomology.Dyadic.ProductFSMPeriodDvd
