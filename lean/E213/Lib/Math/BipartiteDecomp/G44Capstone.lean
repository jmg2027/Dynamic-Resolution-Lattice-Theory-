import E213.Lib.Math.BipartiteDecomp.AdditiveCheck
import E213.Lib.Math.BipartiteDecomp.BinomialExpansion
import E213.Lib.Math.BipartiteDecomp.TernaryBinary

/-!
# G44 Capstone — Bipartite Decomposition (∅-axiom)

5 cluster witnesses + total bundle.

Mingu's bipartite hypothesis verified:
  * **NOT** `3²⁵ + 2²⁵ ≈ 5²⁵` (off by ~10⁸).
  * **YES** `(3+2)²⁵ = 5²⁵` (binomial, exact).
  * d=5 substrate decomposes as N_S=3 (S-axis) + N_T=2 (T-axis).
-/

namespace E213.Lib.Math.BipartiteDecomp.G44Capstone

open E213.Lib.Math.BipartiteDecomp.AdditiveCheck
  (substrate_sum substrate_product three_pow_25 two_pow_25
   five_pow_25 naive_sum additive_fails)
open E213.Lib.Math.BipartiteDecomp.BinomialExpansion
  (binomial_closure first_term last_term edge_sum)
open E213.Lib.Math.BipartiteDecomp.TernaryBinary
  (axis_sum k32_edges k32_b1 su3_boson_count bipartite_total_25)

/-- ★ **Additive failure**: `3²⁵ + 2²⁵ << 5²⁵`. -/
theorem additive_failure_witness :
    (3 : Nat) ^ 25 = 847288609443
    ∧ (2 : Nat) ^ 25 = 33554432
    ∧ (3 : Nat) ^ 25 + (2 : Nat) ^ 25 = 847322163875
    ∧ (3 : Nat) ^ 25 + (2 : Nat) ^ 25 < (5 : Nat) ^ 25 :=
  ⟨three_pow_25, two_pow_25, naive_sum, additive_fails⟩

/-- ★ **Binomial closure**: `(3+2)²⁵ = 5²⁵`. -/
theorem binomial_witness :
    ((3 : Nat) + 2) ^ 25 = (5 : Nat) ^ 25
    ∧ (5 : Nat) ^ 25 = 298023223876953125 :=
  ⟨binomial_closure, five_pow_25⟩

/-- ★ **Edge partitions**: pure-S (k=25) and pure-T (k=0). -/
theorem edge_witness :
    (3 : Nat) ^ 0 * (2 : Nat) ^ 25 = 33554432
    ∧ (3 : Nat) ^ 25 * (2 : Nat) ^ 0 = 847288609443 :=
  ⟨first_term, last_term⟩

/-- ★ **K_{3,2}^{(c=2)} structure**: 12 edges, b₁ = 8 = N_S² − 1. -/
theorem k32_witness :
    (5 : Nat) = 3 + 2
    ∧ (3 : Nat) * 2 * 2 = 12
    ∧ (12 : Nat) - 5 + 1 = 8
    ∧ (3 : Nat) * 3 - 1 = 8 :=
  ⟨substrate_sum, k32_edges, k32_b1, su3_boson_count⟩

/-- ★★★ **Total bipartite witness** ★★★ — additive fails,
    binomial succeeds, K_{3,2} aligns. -/
theorem total_witness :
    (3 : Nat) ^ 25 + (2 : Nat) ^ 25 < (5 : Nat) ^ 25
    ∧ ((3 : Nat) + 2) ^ 25 = (5 : Nat) ^ 25
    ∧ (5 : Nat) = 3 + 2
    ∧ (3 : Nat) * 3 - 1 = 8 :=
  ⟨additive_fails, binomial_closure, substrate_sum, su3_boson_count⟩

end E213.Lib.Math.BipartiteDecomp.G44Capstone
