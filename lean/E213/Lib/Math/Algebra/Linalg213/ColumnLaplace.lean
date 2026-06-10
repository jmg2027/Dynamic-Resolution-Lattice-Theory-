import E213.Lib.Math.Algebra.Linalg213.DetTranspose

/-!
# Linalg213 — Laplace expansion along an arbitrary column (a `det_transpose` corollary)

`Laplace.cofactor_row_i` expands `det` along any **row**; this file is its **column** dual,
obtained for free from `DetTranspose.det_transpose`.  Expanding along column `k` of `M` is
expanding along row `k` of `Mᵀ`, and the cofactor minors match because the minor of a transpose
is the transpose of the minor (`detMinor_transpose_swap`) — the row-skip and column-skip
reindexers `if · < · then · else ·+1` are the *same* function (`colShift`).

  * ★★ `cofactor_col_k` — `det (n+1) M = Σ_{j<n+1} (−1)^(k+j) · M j k · det n (minorAt j k M)`.

All ∅-axiom.
-/

namespace E213.Lib.Math.Algebra.Linalg213.ColumnLaplace

open E213.Lib.Math.Algebra.Linalg213.DetN (det minor det_congr altSign)
open E213.Lib.Math.Algebra.Linalg213.Permutation (iota sumZ)
open E213.Lib.Math.Algebra.Linalg213.Laplace (minorAt cofactor_row_i)
open E213.Lib.Math.Algebra.Linalg213.DetTranspose (transpose det_transpose)
open E213.Lib.Math.Algebra.Linalg213.PermClosure (map_eq_of_mem)

/-- The minor of a transpose is the transpose of the minor (with the skipped row/column
    indices swapped): `det n (minorAt k j Mᵀ) = det n (minorAt j k M)`.  Pointwise these minors
    are defeq — `minorAt`'s row-skip `if i' < i then i' else i'+1` is `colShift i i'`. -/
theorem detMinor_transpose_swap (n k j : Nat) (M : Nat → Nat → Int) :
    det n (minorAt k j (transpose M)) = det n (minorAt j k M) := by
  have hpt : ∀ i' l, minorAt k j (transpose M) i' l = transpose (minorAt j k M) i' l :=
    fun _ _ => rfl
  rw [det_congr n hpt, det_transpose n (minorAt j k M)]

/-- ★★ **Laplace expansion along column `k`.**  For `k < n+1`:
    `det (n+1) M = Σ_{j<n+1} (−1)^(k+j) · M j k · det n (minorAt j k M)` — the column dual of
    `cofactor_row_i`, a corollary of `det_transpose`. -/
theorem cofactor_col_k (M : Nat → Nat → Int) (n k : Nat) (hk : k < n + 1) :
    det (n + 1) M
      = sumZ ((iota (n + 1)).map
          (fun j => altSign (k + j) * M j k * det n (minorAt j k M))) := by
  rw [← det_transpose (n + 1) M, cofactor_row_i (transpose M) n k hk,
      map_eq_of_mem _ _ (fun j _ => by
        show altSign (k + j) * M j k * det n (minorAt k j (transpose M))
           = altSign (k + j) * M j k * det n (minorAt j k M)
        rw [detMinor_transpose_swap n k j M])]

end E213.Lib.Math.Algebra.Linalg213.ColumnLaplace
