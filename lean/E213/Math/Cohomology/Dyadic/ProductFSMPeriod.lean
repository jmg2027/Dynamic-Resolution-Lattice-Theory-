import E213.Math.Cohomology.Dyadic.ProductFSMRun

/-!
# Lens Composition Theorem — period | lcm

Combines `product_bits_eq` (decomposition) with
`bs_combined_periodic_lcm` (LCM stream closure) to obtain:

  period(BitFSM.product f1 f2 g) | lcm(period(f1), period(f2))

This is the **FSM-level CRT multiplicativity** — the structural
"lens composition" theorem.
-/

namespace E213.Math.Cohomology.Dyadic.ProductFSMPeriod

open E213.Math.Cohomology.Dyadic.BitFSM (BitFSM)
open E213.Math.Cohomology.Dyadic.ProductFSM
open E213.Math.Cohomology.Dyadic.ProductFSMRun (product_bits_eq)
open E213.Math.Cohomology.Dyadic.LCMClosure (bs_combined_periodic_lcm)


/-- ★★★★★★ Lens Composition Theorem — period of product divides LCM
    of component periods. -/
theorem lens_composition_period {n m : Nat} (hm : 0 < m)
    (f1 : BitFSM n) (f2 : BitFSM m) (g : Bool → Bool → Bool)
    (p q : Nat) (hp : 0 < p) (hq : 0 < q)
    (h1 : ∀ k, f1.bits (k + p) = f1.bits k)
    (h2 : ∀ k, f2.bits (k + q) = f2.bits k) :
    ∀ k, (BitFSM.product hm f1 f2 g).bits (k + Nat.lcm p q)
        = (BitFSM.product hm f1 f2 g).bits k := by
  intro k
  rw [product_bits_eq, product_bits_eq]
  exact bs_combined_periodic_lcm f1.bits f2.bits p q hp hq h1 h2 g k

/-- ★★★★★★ Variant: same period (square) — period | p when both
    components have period p. -/
theorem lens_composition_same_period {n m : Nat} (hm : 0 < m)
    (f1 : BitFSM n) (f2 : BitFSM m) (g : Bool → Bool → Bool)
    (p : Nat) (hp : 0 < p)
    (h1 : ∀ k, f1.bits (k + p) = f1.bits k)
    (h2 : ∀ k, f2.bits (k + p) = f2.bits k) :
    ∀ k, (BitFSM.product hm f1 f2 g).bits (k + p)
        = (BitFSM.product hm f1 f2 g).bits k := by
  intro k
  rw [product_bits_eq, product_bits_eq]
  rw [h1, h2]

end E213.Math.Cohomology.Dyadic.ProductFSMPeriod
