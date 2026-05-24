import E213.Lib.Math.Cohomology.Cochain.Core
import E213.Lib.Math.Cohomology.Delta.Pointwise
import E213.Lib.Math.Cohomology.Universal.Prop51
import E213.Meta.Tactic.NatHelper

import E213.Lib.Math.Cohomology.Delta.Core
import E213.Lib.Physics.Simplex.Counts

/-!
# Universal Prop-lift at (5, 4) — Δ⁴ 4-cochain (codim-1 stratum)

`Cochain 5 4 = Fin (binom 5 4) → Bool = Fin 5 → Bool`,
`2⁵ = 32` functions.  Sister to `Prop51` (Cochain 5 1, same
dimension) but at the codim-1 stratum.

Used as the β-pattern at CupAW Leibniz bidegree (5, 1, 4).
-/

namespace E213.Lib.Math.Cohomology.Universal.Prop54

open E213.Lib.Physics.Simplex.Counts (binom)
open E213.Lib.Math.Cohomology.Delta.Core (delta)
open E213.Lib.Math.Cohomology.Cochain.Core (Cochain)
open E213.Lib.Math.Cohomology.Delta.Pointwise (delta_pointwise_eq)
open E213.Tactic.NatHelper (cases_lt_five)

/-- Cochain 5 4 parametrized by 5 Bool values. -/
def pattern (b0 b1 b2 b3 b4 : Bool) : Cochain 5 4 := fun i =>
  match i.val with
  | 0 => b0
  | 1 => b1
  | 2 => b2
  | 3 => b3
  | _ => b4

/-- Pointwise pattern equality at (5, 4). -/
theorem pattern_eq_at (σ : Cochain 5 4) (k : Fin (binom 5 4)) :
    σ k = pattern
      (σ ⟨0, by decide⟩) (σ ⟨1, by decide⟩) (σ ⟨2, by decide⟩)
      (σ ⟨3, by decide⟩) (σ ⟨4, by decide⟩) k := by
  obtain ⟨n, hn⟩ := k
  show σ ⟨n, hn⟩ = pattern _ _ _ _ _ ⟨n, hn⟩
  rcases cases_lt_five hn with h | h | h | h | h <;> subst h <;> rfl

end E213.Lib.Math.Cohomology.Universal.Prop54
