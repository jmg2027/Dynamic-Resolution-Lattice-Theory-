import E213.Lib.Math.Cohomology.Cup.RangeFoldXor
import E213.Lib.Math.Cohomology.Cup.FaceIdxGeneral
import E213.Lib.Math.Cohomology.Delta.Pointwise

/-!
# Cohomology.Cup.DeltaUnfoldGeneral

**Fin-level `delta` unfolds to `xorRange`** — bridge between
Lean-core `delta` (defined via `List.range`-foldl with subsetIdx
guards) and the custom `xorRange` of `LeibnizLexListLevel`.

PURE.
-/

namespace E213.Lib.Math.Cohomology.Cup.DeltaUnfoldGeneral

open E213.Lib.Math.Cohomology.Cochain.Core (Cochain)
open E213.Lib.Math.Cohomology.Delta.Core (delta deltaAt subsetIdx)
open E213.Lib.Math.Cohomology.Delta.Pointwise (foldl_step_eq)
open E213.Lib.Math.Cohomology.Examples.SimplexBasis (kSubset)
open E213.Lib.Math.Cohomology.Cup.FaceIdxGeneral
  (faceIdx faceIdxNat faceIdxNat_lt)
open E213.Lib.Math.Cohomology.Cup.RangeFoldXor
  (foldl_xor_range_eq_xorRange)
open E213.Lib.Math.Cohomology.Cup.LeibnizLexListLevel (xorRange xorRange_congr)
open E213.Lib.Physics.Simplex.Counts (binom)

/-- Raw σ-at-face value: σ at the colex index of the i-th eraseIdx
    face of τ, with `false` fallback when subsetIdx escapes range.
    PURE. -/
def sigmaAtFaceRaw (n k : Nat) (σ : Cochain n k)
    (τ_idx : Fin (binom n (k + 1))) (i : Nat) : Bool :=
  let face_i := (kSubset n (k+1) τ_idx.val).eraseIdx i
  let f_idx := subsetIdx n k face_i
  if h : f_idx < binom n k then σ ⟨f_idx, h⟩ else false

/-- Bridge intermediate: rewrite the deltaAt step to `xor acc · raw`.
    The two step functions agree pointwise (xor-false = id). PURE. -/
theorem delta_eq_foldl_xor_raw (n k : Nat) (σ : Cochain n k)
    (τ_idx : Fin (binom n (k + 1))) :
    delta σ τ_idx
    = (List.range (k + 1)).foldl
        (fun acc i => xor acc (sigmaAtFaceRaw n k σ τ_idx i)) false := by
  show deltaAt n k σ τ_idx.val = _
  show (List.range (k + 1)).foldl
        (fun acc i =>
          let face_i := (kSubset n (k+1) τ_idx.val).eraseIdx i
          let f_idx := subsetIdx n k face_i
          if h : f_idx < binom n k then xor acc (σ ⟨f_idx, h⟩) else acc)
        false
      = (List.range (k + 1)).foldl
        (fun acc i => xor acc (sigmaAtFaceRaw n k σ τ_idx i)) false
  apply foldl_step_eq
  intro acc i
  show (let face_i := (kSubset n (k+1) τ_idx.val).eraseIdx i
        let f_idx := subsetIdx n k face_i
        if h : f_idx < binom n k then xor acc (σ ⟨f_idx, h⟩) else acc)
     = xor acc (sigmaAtFaceRaw n k σ τ_idx i)
  show (if h : subsetIdx n k ((kSubset n (k+1) τ_idx.val).eraseIdx i)
              < binom n k
        then xor acc (σ ⟨_, h⟩) else acc)
     = xor acc
       (if h : subsetIdx n k ((kSubset n (k+1) τ_idx.val).eraseIdx i)
              < binom n k
        then σ ⟨_, h⟩ else false)
  by_cases h_lt : subsetIdx n k ((kSubset n (k+1) τ_idx.val).eraseIdx i)
                  < binom n k
  · rw [dif_pos h_lt, dif_pos h_lt]
  · rw [dif_neg h_lt, dif_neg h_lt]
    cases acc <;> rfl

/-- ★★★ **delta unfold via xorRange** — Fin-level `delta` equals
    `xorRange (k+1)` over the raw σ-at-face function.  PURE. -/
theorem delta_eq_xorRange (n k : Nat) (σ : Cochain n k)
    (τ_idx : Fin (binom n (k + 1))) :
    delta σ τ_idx = xorRange (k + 1) (sigmaAtFaceRaw n k σ τ_idx) := by
  rw [delta_eq_foldl_xor_raw]
  rw [foldl_xor_range_eq_xorRange]
  cases xorRange (k + 1) (sigmaAtFaceRaw n k σ τ_idx) <;> rfl

/-- ★★ **`sigmaAtFaceRaw` collapses to σ at `faceIdx` when `i < k+1`** —
    the subsetIdx guard always succeeds for in-range face positions.
    PURE. -/
theorem sigmaAtFaceRaw_eq_faceIdx (n k : Nat) (σ : Cochain n k)
    (τ_idx : Fin (binom n (k + 1))) (i : Nat) (h_i : i < k + 1) :
    sigmaAtFaceRaw n k σ τ_idx i = σ (faceIdx n (k + 1) i h_i τ_idx) := by
  have h_face_lt :
      subsetIdx n k ((kSubset n (k+1) τ_idx.val).eraseIdx i) < binom n k :=
    faceIdxNat_lt n (k+1) i τ_idx.val h_i τ_idx.isLt
  show (if h : subsetIdx n k _ < binom n k then σ ⟨_, h⟩ else false)
     = σ (faceIdx n (k+1) i h_i τ_idx)
  rw [dif_pos h_face_lt]
  rfl

/-- ★★★★ **delta via faceIdx** — the clean Fin-level statement,
    inside the `xorRange` range every face value is just
    `σ (faceIdx _ _ _ _ τ)`.  PURE via `xorRange_congr`. -/
theorem delta_via_faceIdx_xorRange (n k : Nat) (σ : Cochain n k)
    (τ_idx : Fin (binom n (k + 1))) :
    delta σ τ_idx = xorRange (k + 1)
      (fun i => if h : i < k + 1
                then σ (faceIdx n (k + 1) i h τ_idx)
                else false) := by
  rw [delta_eq_xorRange]
  apply xorRange_congr
  intro i h_i
  rw [sigmaAtFaceRaw_eq_faceIdx n k σ τ_idx i h_i]
  rw [dif_pos h_i]

end E213.Lib.Math.Cohomology.Cup.DeltaUnfoldGeneral
