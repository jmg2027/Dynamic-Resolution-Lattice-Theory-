import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinConvAssoc
import E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinConvComm

/-!
# Reassociating `(a·b)·(a·b) = (a·a)·(b·b)` in the group ring (∅-axiom, Phase A3 / route b)

In the commutative ring `R[C_p]` (convolution: bilinear + `conv_comm` + `conv_assoc`),

  `(a ⋆ b) ⋆ (a ⋆ b) = (a ⋆ a) ⋆ (b ⋆ b)`   (`conv_four_swap`, coefficientwise, `k < p`).

The standard four-factor reassociation `(ab)(ab) = a(b(ab)) = a((ba)b) = a((ab)b) = a(a(bb)) =
(aa)(bb)`.  Applied to `a = g(χ)`, `b = conj g(χ)` it turns `(g·ḡ)² = Y²` into `(g·g)·(ḡ·ḡ)`, the
identity that — with `g·g = J·g(χ²)` and `Y² = p·Y` — yields the Jacobi-sum norm `N(J)=p`.  ∅-axiom.
-/

namespace E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinConvFourSwap

open E213.Lib.Math.Algebra.CayleyDickson.Integer.ZOmega (ZOmega)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinGroupRing (conv conv_congr)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinConvComm (conv_comm)
open E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinConvAssoc (conv_assoc)

/-- `b ⋆ (a ⋆ b) = a ⋆ (b ⋆ b)` (coefficientwise, `j < p`): `b(ab) = (ba)b = (ab)b = a(bb)`. -/
private theorem conv_bab (p : Nat) (a b : Nat → ZOmega) {j : Nat} (hp : 0 < p) (hj : j < p) :
    conv p b (fun j' => conv p a b j') j = conv p a (fun j' => conv p b b j') j := by
  rw [← conv_assoc p b a b hj,
      conv_congr p j hp (fun i hi => conv_comm p b a hi) (fun _ _ => rfl)]
  exact conv_assoc p a b b hj

/-- ★★★★★ **Four-factor reassociation** — `(a⋆b)⋆(a⋆b) = (a⋆a)⋆(b⋆b)` (coefficientwise, `k < p`).
    `conv_assoc` + `conv_bab` (which carries the one `conv_comm`).  ∅-axiom. -/
theorem conv_four_swap (p : Nat) (a b : Nat → ZOmega) {k : Nat} (hk : k < p) :
    conv p (fun j => conv p a b j) (fun j => conv p a b j) k
      = conv p (fun j => conv p a a j) (fun j => conv p b b j) k := by
  have hp : 0 < p := Nat.lt_of_le_of_lt (Nat.zero_le k) hk
  rw [conv_assoc p a b (fun j => conv p a b j) hk,
      conv_congr p k hp (fun _ _ => rfl) (fun i hi => conv_bab p a b hp hi)]
  exact (conv_assoc p a a (fun j => conv p b b j) hk).symm

end E213.Lib.Math.Algebra.CayleyDickson.Integer.EisensteinConvFourSwap
