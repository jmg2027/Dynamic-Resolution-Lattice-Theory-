import E213.Math.Modulus.HasModulus

/-!
# DiagonalHasModulus: HasModulus for the diagonal sequence

The sequence `abLens.view (xs n) = (n+1, n+1)` (diagonal pair) has a
HasModulus instance.  N(m, k) = 0 (orderProj is already constant for
every n).

Together with PellHasModulus, this is the second concrete instance —
a demonstration of the applicability of the HasModulus typeclass.
-/

namespace E213.Math.Diagonal.HasModulus

open E213.Firmware E213.Lens
open E213.Lens.Instances.AB
open E213.Math.Cauchy.Archimedean
open E213.Math.Modulus.HasModulus

/-- HasModulus instance for the diagonal sequence.  No omega. -/
def diagonalHasModulus (xs : Nat → Raw)
    (h : ∀ n, abLens.view (xs n) = (n + 1, n + 1)) :
    HasModulus xs where
  N := fun _ _ => 0
  cauchy_at := by
    intro m k _ i j _ _
    rw [h i, h j]
    rw [diagonal_seq_orderProj_const m k (i+1) (Nat.succ_le_succ (Nat.zero_le _)),
        diagonal_seq_orderProj_const m k (j+1) (Nat.succ_le_succ (Nat.zero_le _))]

end E213.Math.Diagonal.HasModulus
