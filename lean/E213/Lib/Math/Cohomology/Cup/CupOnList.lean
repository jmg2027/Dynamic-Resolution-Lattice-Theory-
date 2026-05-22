import E213.Lib.Math.Cohomology.Cup.FaceIdxGeneral
import E213.Lib.Math.Cohomology.Cup.FinBridgeGeneral

/-!
# Cohomology.Cup.CupOnList

Bridge layer between the **List-level** ∀(k,l) twisted Leibniz
(`LeibnizLexListLevel.list_level_leibniz_general`) and the
**Fin-indexed** cup (`cup`).

Defines `cupOnList`: the cup product **evaluated at a sorted Nat-list**
(rather than at a Fin colex index), using `subsetIdx` to look up
the cochain values.  Key property:

  `cup n k l α β τ_idx = cupOnList n k l α β (kSubset n (k+l) τ_idx.val)`

Composed with `kSubset_faceIdxNat_eq`, this gives:

  `cup n k l α β (faceIdx n m i h_i τ)
    = cupOnList n k l α β ((kSubset n m τ.val).eraseIdx i)`

— the foundational bridge for evaluating Fin-indexed cup at face
positions in terms of List operations.

PURE.
-/

namespace E213.Lib.Math.Cohomology.Cup.CupOnList

open E213.Lib.Math.Cohomology.Cochain.Core (Cochain)
open E213.Lib.Math.Cohomology.Cup.Core (cup)
open E213.Lib.Math.Cohomology.Delta.Core (subsetIdx)
open E213.Lib.Math.Cohomology.Examples.SimplexBasis (kSubset)
open E213.Lib.Math.Cohomology.Cup.FaceIdxGeneral
  (faceIdx faceIdxNat faceIdxNat_lt kSubset_faceIdxNat_eq)
open E213.Lib.Physics.Simplex.Counts (binom)

/-- ★ **cup product evaluated at a Nat list** — uses `subsetIdx` to
    map the take/drop into Fin colex indices, falling back to `false`
    if either index is out of range.  Mirrors the structure of
    `Cup.Core.cup` but takes a list directly.  PURE. -/
def cupOnList (n k l : Nat) (α : Cochain n k) (β : Cochain n l)
    (s : List Nat) : Bool :=
  let f_idx := subsetIdx n k (s.take k)
  let b_idx := subsetIdx n l (s.drop k)
  if hf : f_idx < binom n k then
    if hb : b_idx < binom n l then α ⟨f_idx, hf⟩ && β ⟨b_idx, hb⟩
    else false
  else false

/-- ★★ **cup ↔ cupOnList equivalence on `kSubset`** — for any Fin-indexed
    `τ_idx`, the Fin-level `cup` equals the List-level `cupOnList`
    evaluated at the corresponding kSubset list.  PURE — direct unfolding. -/
theorem cup_eq_cupOnList_kSubset (n k l : Nat)
    (α : Cochain n k) (β : Cochain n l)
    (τ_idx : Fin (binom n (k + l))) :
    cup n k l α β τ_idx
    = cupOnList n k l α β (kSubset n (k + l) τ_idx.val) := by
  rfl

/-- ★★★ **Fin-level cup at face = cupOnList at eraseIdx** — the
    foundational bridge for the Fin-level twisted Leibniz.

    Specialised to `m = k+l+1` so the face index lands in
    `Fin (binom n ((k+l+1)-1)) = Fin (binom n (k+l))` —
    exactly the input type for `cup n k l α β`.

    Combines `cup_eq_cupOnList_kSubset` + `kSubset_faceIdxNat_eq`.
    PURE. -/
theorem cup_at_faceIdx_eq_cupOnList_eraseIdx
    (n k l i : Nat) (h_im : i < k + l + 1)
    (α : Cochain n k) (β : Cochain n l)
    (τ : Fin (binom n (k + l + 1))) :
    cup n k l α β (faceIdx n (k + l + 1) i h_im τ)
    = cupOnList n k l α β ((kSubset n (k + l + 1) τ.val).eraseIdx i) := by
  rw [cup_eq_cupOnList_kSubset]
  congr 1
  show kSubset n (k + l + 1 - 1) (faceIdxNat n (k + l + 1) i τ.val)
       = (kSubset n (k + l + 1) τ.val).eraseIdx i
  exact kSubset_faceIdxNat_eq n (k + l + 1) i τ.val h_im τ.isLt

end E213.Lib.Math.Cohomology.Cup.CupOnList
