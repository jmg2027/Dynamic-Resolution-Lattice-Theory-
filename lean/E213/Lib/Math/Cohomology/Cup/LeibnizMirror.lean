import E213.Lib.Math.Cohomology.Cup.LeibnizFinGeneral

/-!
# Cohomology.Cup.LeibnizMirror — reverse-lex cup + mirror Leibniz

Mirror (s = l) of the lex-projection cup product (s = k).  The two
choices `(s = k, s = l)` exhaust the count-Lens-canonical sorted
single-partition recipes that yield a valid `Cochain k × Cochain l
→ Cochain (k+l)` signature.

The mirror cup is the swap-relabeling of `cup`:

  `cupRev n k l α β = cup n l k β α`

up to Bool AND commutativity.  Its δ-closure has the correction
term at the **mirror** middle vertex `τ[l]` (instead of `τ[k]` for
the lex-projection cup).

PURE.  All theorems direct corollaries of `fin_level_leibniz_general`.
-/

namespace E213.Lib.Math.Cohomology.Cup.LeibnizMirror

open E213.Lib.Math.Cohomology.Cochain.Core (Cochain)
open E213.Lib.Math.Cohomology.Cup.Core (cup)
open E213.Lib.Math.Cohomology.Delta.Core (delta subsetIdx)
open E213.Lib.Math.Cohomology.Examples.SimplexBasis (kSubset)
open E213.Lib.Math.Cohomology.Cup.FaceIdxGeneral (faceIdx)
open E213.Lib.Math.Cohomology.Cup.LeibnizFinGeneral
  (asListCochain fin_level_leibniz_general)
open E213.Lib.Math.Cohomology.Cup.LeibnizLexListLevel (cupList deltaListR)
open E213.Lib.Physics.Simplex.Counts (binom)

/-! ## §1.  Reverse-lex cup definition -/

/-- ★ **Reverse-lex cup** — mirror of `cup`.  Front `l` vertices
    go to β, back `k` to α.  Equivalent to `cup n l k β α` up to
    Bool AND commutativity.  PURE. -/
def cupRev (n k l : Nat) (α : Cochain n k) (β : Cochain n l) :
    Cochain n (k + l) :=
  fun τ_idx =>
    let τ := kSubset n (k + l) τ_idx.val
    let front_l := τ.take l
    let back_k := τ.drop l
    let b_idx := subsetIdx n l front_l
    let a_idx := subsetIdx n k back_k
    if hb : b_idx < binom n l then
      if ha : a_idx < binom n k then
        α ⟨a_idx, ha⟩ && β ⟨b_idx, hb⟩
      else false
    else false

/-- ★★ **`cupRev` is `cup` with swapped factors** — for any
    `(n, k, l)`, `cupRev n k l α β τ = cup n l k β α τ'`
    where `τ'` lives in the same Fin type (binom is symmetric in
    `k ↔ l` since `(k+l) = (l+k)` by Nat.add_comm).  PURE.

    The Bool && commutativity bridges `α x && β y = β y && α x`. -/
theorem cupRev_eq_cup_swapped (n k l : Nat) (α : Cochain n k)
    (β : Cochain n l) (τ_idx : Fin (binom n (k + l))) :
    cupRev n k l α β τ_idx
    = cup n l k β α
        ⟨τ_idx.val, (congrArg (binom n) (Nat.add_comm k l)) ▸ τ_idx.isLt⟩ := by
  show (if hb : subsetIdx n l ((kSubset n (k+l) τ_idx.val).take l) < binom n l
        then (if ha : subsetIdx n k ((kSubset n (k+l) τ_idx.val).drop l) < binom n k
              then α ⟨_, ha⟩ && β ⟨_, hb⟩ else false) else false)
      = (if hf : subsetIdx n l ((kSubset n (l+k) τ_idx.val).take l) < binom n l
         then (if hg : subsetIdx n k ((kSubset n (l+k) τ_idx.val).drop l) < binom n k
               then β ⟨_, hf⟩ && α ⟨_, hg⟩ else false) else false)
  have h_lists_eq : kSubset n (k+l) τ_idx.val = kSubset n (l+k) τ_idx.val :=
    congrArg (fun m => kSubset n m τ_idx.val) (Nat.add_comm k l)
  rw [h_lists_eq]
  by_cases hb : subsetIdx n l ((kSubset n (l+k) τ_idx.val).take l) < binom n l
  · rw [dif_pos hb, dif_pos hb]
    by_cases ha : subsetIdx n k ((kSubset n (l+k) τ_idx.val).drop l) < binom n k
    · rw [dif_pos ha, dif_pos ha]
      cases α ⟨_, ha⟩ <;> cases β ⟨_, hb⟩ <;> rfl
    · rw [dif_neg ha, dif_neg ha]
  · rw [dif_neg hb, dif_neg hb]

/-! ## §2.  Mirror Leibniz — list level -/

open E213.Lib.Math.Cohomology.Cup.LeibnizLexListLevel
  (xorRange list_level_leibniz_general)

/-- ★★★ **Mirror twisted Leibniz at the list level** — direct
    corollary of `list_level_leibniz_general` with the bidegree
    swap `(k, l) ↦ (l, k)`.  The correction lives at position `l`
    (the mirror of `k`).  PURE.

    For any `(k, l : Nat)`, any `α β : List Nat → Bool`, and any
    list `τ`:

      xorRange (l + k + 1) (fun i => cupList l k β α (τ.eraseIdx i))
      = xor (xor (cupList (l + 1) k (deltaListR l β) α τ)
                 (cupList l (k + 1) β (deltaListR k α) τ))
            (cupList l k β α (τ.eraseIdx l))

    Catalog row 3 (reverse-lex single-partition; see
    `theory/math/cohomology/cup.md` self-reference section).  At
    the Fin level, transferring via `cupRev_eq_cup_swapped` +
    Fin.cast over `k+l = l+k`. -/
theorem list_level_leibniz_mirror (k l : Nat)
    (α β : List Nat → Bool) (τ : List Nat) :
    xorRange (l + k + 1) (fun i => cupList l k β α (τ.eraseIdx i))
    = xor (xor (cupList (l + 1) k (deltaListR l β) α τ)
               (cupList l (k + 1) β (deltaListR k α) τ))
          (cupList l k β α (τ.eraseIdx l)) :=
  list_level_leibniz_general l k β α τ

end E213.Lib.Math.Cohomology.Cup.LeibnizMirror
