import E213.Lib.Math.DyadicFSM.Product.ProductFSMRun

import E213.Lib.Math.DyadicFSM.BitFSM
import E213.Lib.Math.DyadicFSM.Product.LCMClosure
import E213.Lib.Math.DyadicFSM.Product.ProductFSM
/-!
# Lens Composition Theorem — period | p * q

Combines `product_bits_eq` (decomposition) with
`bs_combined_periodic_product` (CRT stream closure at the trivial
common multiple `p * q`) to obtain:

  period(BitFSM.product f1 f2 g) | period(f1) * period(f2)

This is the **FSM-level CRT multiplicativity** — the structural
"lens composition" theorem.  Uses the `p * q` common multiple
rather than `Nat.lcm p q` to remain ∅-axiom (Lean-core `Nat.lcm`
brings `propext` via well-founded gcd termination).
-/

namespace E213.Lib.Math.DyadicFSM.Product.ProductFSMPeriod

open E213.Lib.Math.DyadicFSM.BitFSM (BitFSM)
open E213.Lib.Math.DyadicFSM.Product.ProductFSM
open E213.Lib.Math.DyadicFSM.Product.ProductFSMRun (product_bits_eq)
open E213.Lib.Math.DyadicFSM.Product.LCMClosure (bs_combined_periodic_product)


/-- ★★★★★★ Lens Composition Theorem — product FSM is periodic at
    `p * q`, i.e., period of product divides `p * q`. -/
theorem lens_composition_period {n m : Nat} (hm : 0 < m)
    (f1 : BitFSM n) (f2 : BitFSM m) (g : Bool → Bool → Bool)
    (p q : Nat) (hp : 0 < p) (hq : 0 < q)
    (h1 : ∀ k, f1.bits (k + p) = f1.bits k)
    (h2 : ∀ k, f2.bits (k + q) = f2.bits k) :
    ∀ k, (BitFSM.product hm f1 f2 g).bits (k + p * q)
        = (BitFSM.product hm f1 f2 g).bits k := by
  intro k
  rw [product_bits_eq, product_bits_eq]
  exact bs_combined_periodic_product f1.bits f2.bits p q hp hq h1 h2 g k

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

end E213.Lib.Math.DyadicFSM.Product.ProductFSMPeriod
