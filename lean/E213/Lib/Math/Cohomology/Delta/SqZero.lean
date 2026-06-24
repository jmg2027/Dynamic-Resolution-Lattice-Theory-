import E213.Lib.Math.Cohomology.Delta.Core

import E213.Lib.Math.Cohomology.Cochain.Core
import E213.Lib.Physics.Simplex.Counts
/-!
# Cohomology — δ² = 0

The fundamental cochain identity.  In ℤ/2 (Bool, XOR), each
(k+2)-subset's value under δ²σ counts each k-subset face twice
(once via each removal-order) — XOR of equal values is false.

This file establishes δ²=0 by `decide` at concrete cochains.
The **universally-quantified** version (`∀ σ : Cochain n k, δ²σ = 0`)
is closed at each fixed dimension in `Universal/` — `Prop.dsq_zero_prop_5_0`,
`Prop51`–`Prop53` (`5 1`–`5 3`), and `Prop61` (`6 1`) — by lifting a
Bool-pattern `decide` through the funext-free `Delta.Pointwise.delta_pointwise_eq`,
bypassing the missing `Fintype`/`DecidablePred` on `Cochain n k`.  They are
assembled into the chain-complex structure theorem `ChainComplex.atomic_chain_complex`.

The remaining open frontier is the **dimension-free** `∀ n k σ, δ²σ = 0`
(uniform in `n`), which `decide`/pattern cannot reach — see
`research-notes/frontiers/the_dimension_free_dsquared.md`.
-/

namespace E213.Lib.Math.Cohomology.Delta.SqZero

open E213.Lib.Physics.Simplex.Counts (binom d NS NT)
open E213.Lib.Math.Cohomology.Cochain.Core (Cochain)
open E213.Lib.Math.Cohomology.Delta.Core (delta)

/-- δ²(zero) at (3, 0). -/
theorem delta_sq_zero_zero_3_0 :
    ∀ i : Fin (binom 3 2), delta (delta (Cochain.zero 3 0)) i = false := by
  decide

/-- δ²(zero) at (5, 0). -/
theorem delta_sq_zero_zero_5_0 :
    ∀ i : Fin (binom 5 2), delta (delta (Cochain.zero 5 0)) i = false := by
  decide

/-- δ²(zero) at (5, 1). -/
theorem delta_sq_zero_zero_5_1 :
    ∀ i : Fin (binom 5 3), delta (delta (Cochain.zero 5 1)) i = false := by
  decide

/-- Vertex-0 indicator on n=5 vertices. -/
def vertex0_n5 : Cochain 5 1 := fun i => i.val = 0

/-- δ²(vertex0_n5) = zero — concrete simplicial identity at n=5. -/
theorem delta_sq_vertex0_n5 :
    ∀ i : Fin (binom 5 3), delta (delta vertex0_n5) i = false := by
  decide

/-- Vertex-2 indicator on n=5 vertices. -/
def vertex2_n5 : Cochain 5 1 := fun i => i.val = 2

theorem delta_sq_vertex2_n5 :
    ∀ i : Fin (binom 5 3), delta (delta vertex2_n5) i = false := by
  decide

/-- Edge [0,1] indicator on n=5 (colex idx 0). -/
def edge01_n5 : Cochain 5 2 := fun i => i.val = 0

theorem delta_sq_edge01_n5 :
    ∀ i : Fin (binom 5 4), delta (delta edge01_n5) i = false := by
  decide

/-- Constant-true cochain at (3, 1). -/
def all_true_3_1 : Cochain 3 1 := fun _ => true

theorem delta_sq_all_true_3_1 :
    ∀ i : Fin (binom 3 3), delta (delta all_true_3_1) i = false := by
  decide

/-- ★ capstone: δ²=0 at every tested cochain on Δ⁴. -/
theorem phase_CA_delta_sq_zero :
    (∀ i : Fin (binom 5 3), delta (delta (Cochain.zero 5 1)) i = false)
    ∧ (∀ i : Fin (binom 5 3), delta (delta vertex0_n5) i = false)
    ∧ (∀ i : Fin (binom 5 3), delta (delta vertex2_n5) i = false)
    ∧ (∀ i : Fin (binom 5 4), delta (delta edge01_n5) i = false) := by
  decide

end E213.Lib.Math.Cohomology.Delta.SqZero
