import E213.Lib.Math.Cohomology.Cup.KSubsetEraseIdx
import E213.Lib.Math.Cohomology.Cup.SubsetIdxRoundtripGeneral

/-!
# Cohomology.Cup.FaceIdxGeneral

General face-index function for the `cup` Leibniz bridge:

  `faceIdx n m i (τ : Fin (binom n m)) : Fin (binom n (m-1))`

For each face position `i < m` and each colex index `τ` of an
`m`-subset, returns the colex index of `(kSubset n m τ).eraseIdx i`,
which is itself a valid `(m-1)`-subset by `kSubset_eraseIdx_eq`.

Concretely:

  `faceIdx n m i τ = subsetIdx n (m-1) ((kSubset n m τ.val).eraseIdx i)`

PURE.  Built on `kSubset_eraseIdx_eq` + `roundtrip_n_k`.
-/

namespace E213.Lib.Math.Cohomology.Cup.FaceIdxGeneral

open E213.Lib.Math.Cohomology.Examples.SimplexBasis (kSubset)
open E213.Lib.Math.Cohomology.Delta.Core (subsetIdx)
open E213.Lib.Math.Cohomology.Cup.KSubsetEraseIdx (kSubset_eraseIdx_eq)
open E213.Lib.Math.Cohomology.Cup.SubsetIdxRoundtrip (roundtrip_n_k)
open E213.Lib.Physics.Simplex.Counts (binom)

/-- ★ `faceIdxNat` — Nat-level face index for the i-th face of an
    m-subset (1 ≤ i < m+1, 0 ≤ τ < binom n m).  Returns the colex
    index of the resulting (m-1)-subset.  PURE. -/
def faceIdxNat (n m i τ : Nat) : Nat :=
  subsetIdx n (m - 1) ((kSubset n m τ).eraseIdx i)

/-- ★★ **faceIdx boundedness** — when `i < m` and `τ < binom n m`,
    the face-index `faceIdxNat n m i τ` is strictly less than
    `binom n (m-1)`.  PURE. -/
theorem faceIdxNat_lt (n m i τ : Nat) (h_im : i < m) (h_τ : τ < binom n m) :
    faceIdxNat n m i τ < binom n (m - 1) := by
  obtain ⟨j_e, h_je_lt, h_eq⟩ := kSubset_eraseIdx_eq n m i h_im τ h_τ
  show subsetIdx n (m - 1) ((kSubset n m τ).eraseIdx i) < binom n (m - 1)
  rw [h_eq, roundtrip_n_k n (m - 1) j_e h_je_lt]
  exact h_je_lt

/-- ★★ **Round-trip identity** — the kSubset corresponding to
    `faceIdxNat n m i τ` IS the eraseIdx of the original kSubset.
    PURE. -/
theorem kSubset_faceIdxNat_eq (n m i τ : Nat)
    (h_im : i < m) (h_τ : τ < binom n m) :
    kSubset n (m - 1) (faceIdxNat n m i τ)
    = (kSubset n m τ).eraseIdx i := by
  obtain ⟨j_e, h_je_lt, h_eq⟩ := kSubset_eraseIdx_eq n m i h_im τ h_τ
  show kSubset n (m - 1) (subsetIdx n (m - 1) ((kSubset n m τ).eraseIdx i))
       = (kSubset n m τ).eraseIdx i
  rw [h_eq, roundtrip_n_k n (m - 1) j_e h_je_lt]

/-- ★★★ `faceIdx` — Fin-typed face index, packaging
    `faceIdxNat` + `faceIdxNat_lt`.  Maps `Fin (binom n m)`
    via face position `i < m` to `Fin (binom n (m-1))`.  PURE. -/
def faceIdx (n m i : Nat) (h_im : i < m) (τ : Fin (binom n m)) :
    Fin (binom n (m - 1)) :=
  ⟨faceIdxNat n m i τ.val,
   faceIdxNat_lt n m i τ.val h_im τ.isLt⟩

end E213.Lib.Math.Cohomology.Cup.FaceIdxGeneral
