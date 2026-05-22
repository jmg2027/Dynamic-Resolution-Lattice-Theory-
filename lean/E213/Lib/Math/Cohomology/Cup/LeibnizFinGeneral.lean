import E213.Lib.Math.Cohomology.Cup.CupOnList
import E213.Lib.Math.Cohomology.Cup.DeltaUnfoldGeneral

/-!
# Cohomology.Cup.LeibnizFinGeneral

**Fin-level ∀(n, k, l) twisted Leibniz for the lex-projection cup.**

The capstone bridge — assembles `list_level_leibniz_general` (the
PURE algebraic ∀(k,l) result) into a Fin-typed statement over the
project's standard `Cup.Core.cup` / `Delta.Core.delta` operations.

PURE.
-/

namespace E213.Lib.Math.Cohomology.Cup.LeibnizFinGeneral

open E213.Lib.Math.Cohomology.Cochain.Core (Cochain)
open E213.Lib.Math.Cohomology.Cup.Core (cup)
open E213.Lib.Math.Cohomology.Delta.Core (delta subsetIdx)
open E213.Lib.Math.Cohomology.Examples.SimplexBasis (kSubset)
open E213.Lib.Math.Cohomology.Cup.FaceIdxGeneral
  (faceIdx faceIdxNat faceIdxNat_lt kSubset_faceIdxNat_eq)
open E213.Lib.Math.Cohomology.Cup.CupOnList
  (cupOnList cup_eq_cupOnList_kSubset cup_at_faceIdx_eq_cupOnList_eraseIdx)
open E213.Lib.Math.Cohomology.Cup.DeltaUnfoldGeneral
  (sigmaAtFaceRaw delta_eq_xorRange delta_via_faceIdx_xorRange)
open E213.Lib.Math.Cohomology.Cup.LeibnizLexListLevel
  (cupList deltaListR xorRange xorRange_congr list_level_leibniz_general)
open E213.Lib.Physics.Simplex.Counts (binom)

/-! ## §1.  `asListCochain` — Fin-cochain as List-cochain -/

/-- ★ `asListCochain` — wrap a Fin-indexed cochain `α : Cochain n k`
    as a `List Nat → Bool` function via `subsetIdx`.  PURE. -/
def asListCochain (n k : Nat) (α : Cochain n k) : List Nat → Bool :=
  fun s =>
    let f := subsetIdx n k s
    if h : f < binom n k then α ⟨f, h⟩ else false

/-- ★★ `cupOnList = cupList ∘ asListCochain` — when both factors are
    wrapped through `asListCochain`, `cupOnList` reduces to the
    pure `cupList` of `LeibnizLexListLevel`.  PURE.

    Proof: case-split both subsetIdx guards.  When both true: both
    sides = α ⟨..⟩ && β ⟨..⟩.  When either false: both sides = false. -/
theorem cupOnList_eq_cupList (n k l : Nat) (α : Cochain n k) (β : Cochain n l)
    (s : List Nat) :
    cupOnList n k l α β s
    = cupList k l (asListCochain n k α) (asListCochain n l β) s := by
  unfold cupOnList cupList asListCochain
  by_cases h_f : subsetIdx n k (s.take k) < binom n k
  · by_cases h_b : subsetIdx n l (s.drop k) < binom n l
    · rw [dif_pos h_f, dif_pos h_b, dif_pos h_f, dif_pos h_b]
    · rw [dif_pos h_f, dif_neg h_b, dif_pos h_f, dif_neg h_b]
      cases α ⟨_, h_f⟩ <;> rfl
  · rw [dif_neg h_f, dif_neg h_f]
    rfl

/-! ## §2.  `delta = deltaListR ∘ asListCochain` bridge -/

/-- ★★★ **Fin-delta corresponds to deltaListR over `asListCochain`** —
    the σ-side bridge for the Fin Leibniz assembly.  PURE. -/
theorem delta_eq_deltaListR (n k : Nat) (σ : Cochain n k)
    (τ_idx : Fin (binom n (k + 1))) :
    delta σ τ_idx
    = deltaListR k (asListCochain n k σ) (kSubset n (k+1) τ_idx.val) := by
  rw [delta_eq_xorRange]
  show xorRange (k + 1) (sigmaAtFaceRaw n k σ τ_idx)
     = xorRange (k + 1)
         (fun i => asListCochain n k σ
                   ((kSubset n (k+1) τ_idx.val).eraseIdx i))
  apply xorRange_congr
  intro i _
  rfl

/-! ## §3.  `delta(cup) = xorRange of cupOnList at eraseIdx` -/

/-- ★★★★ **The key intermediate** — `delta` of a `cup` value
    unfolds to an `xorRange` of `cupOnList` evaluated at each
    eraseIdx face of the kSubset list.

    Composes `delta_eq_xorRange` (Fin-delta as xorRange of
    sigmaAtFaceRaw) with `cup_eq_cupOnList_kSubset` (Fin-cup as
    cupOnList at kSubset) + `kSubset_faceIdxNat_eq` (the face
    kSubset equals the eraseIdx list).  PURE.  -/
theorem delta_cup_eq_xorRange_cupOnList
    (n k l : Nat) (α : Cochain n k) (β : Cochain n l)
    (τ : Fin (binom n (k + l + 1))) :
    delta (cup n k l α β) τ
    = xorRange (k + l + 1) (fun i =>
        cupOnList n k l α β ((kSubset n (k + l + 1) τ.val).eraseIdx i)) := by
  rw [delta_eq_xorRange]
  apply xorRange_congr
  intro i h_i
  -- Goal: sigmaAtFaceRaw n (k+l) (cup α β) τ i
  --      = cupOnList n k l α β ((kSubset _ τ).eraseIdx i)
  show (if h : subsetIdx n (k+l) ((kSubset n (k+l+1) τ.val).eraseIdx i)
              < binom n (k+l)
        then (cup n k l α β) ⟨_, h⟩ else false)
     = cupOnList n k l α β ((kSubset n (k+l+1) τ.val).eraseIdx i)
  have h_lt : subsetIdx n (k+l) ((kSubset n (k+l+1) τ.val).eraseIdx i)
              < binom n (k+l) :=
    faceIdxNat_lt n (k+l+1) i τ.val h_i τ.isLt
  rw [dif_pos h_lt]
  -- Use cup_eq_cupOnList_kSubset + kSubset_faceIdxNat_eq:
  rw [cup_eq_cupOnList_kSubset]
  congr 1
  show kSubset n (k+l)
       (subsetIdx n (k+l) ((kSubset n (k+l+1) τ.val).eraseIdx i))
     = (kSubset n (k+l+1) τ.val).eraseIdx i
  exact kSubset_faceIdxNat_eq n (k+l+1) i τ.val h_i τ.isLt

/-! ## §4.  Capstone — Fin-level ∀(n, k, l) twisted Leibniz -/

/-- ★★★★★★ **Fin-level ∀(n, k, l) twisted Leibniz** — THE result.

    For any `(n, k, l)`, any cochains `α : Cochain n k`,
    `β : Cochain n l`, and any colex index `τ : Fin (binom n (k+l+1))`:

      delta (cup n k l α β) τ
        = xor (xor (cupList (k+1) l (deltaListR k α') β' τ_list)
                   (cupList k (l+1) α' (deltaListR l β') τ_list))
              (cup n k l α β (faceIdx n (k+l+1) k h_k τ))

    where `α' = asListCochain n k α`, `β' = asListCochain n l β`,
    `τ_list = kSubset n (k+l+1) τ.val`, `h_k : k < k+l+1`.

    The middle-removed face on the RHS uses the Fin-indexed `cup`
    via `faceIdx`; the two side terms remain in `cupList`+`deltaListR`
    form (the Fin-level conversion of these is a separate plumbing
    step — see `delta_eq_deltaListR`).

    Composes `delta_cup_eq_xorRange_cupOnList`,
    `cupOnList_eq_cupList`, `list_level_leibniz_general`, and
    `cup_at_faceIdx_eq_cupOnList_eraseIdx`.  PURE. -/
theorem fin_level_leibniz_general
    (n k l : Nat) (α : Cochain n k) (β : Cochain n l)
    (τ : Fin (binom n (k + l + 1))) :
    delta (cup n k l α β) τ
    = xor (xor (cupList (k+1) l
                  (deltaListR k (asListCochain n k α))
                  (asListCochain n l β)
                  (kSubset n (k+l+1) τ.val))
               (cupList k (l+1)
                  (asListCochain n k α)
                  (deltaListR l (asListCochain n l β))
                  (kSubset n (k+l+1) τ.val)))
          (cup n k l α β (faceIdx n (k+l+1) k
            (Nat.lt_succ_of_le (Nat.le_add_right k l)) τ)) := by
  -- Step 1: LHS = xorRange of cupOnList at eraseIdx
  rw [delta_cup_eq_xorRange_cupOnList]
  -- Step 2: convert each cupOnList to cupList
  have h_cong :
      xorRange (k + l + 1) (fun i =>
        cupOnList n k l α β ((kSubset n (k+l+1) τ.val).eraseIdx i))
      = xorRange (k + l + 1) (fun i =>
        cupList k l (asListCochain n k α) (asListCochain n l β)
                ((kSubset n (k+l+1) τ.val).eraseIdx i)) := by
    apply xorRange_congr
    intro i _
    exact cupOnList_eq_cupList n k l α β _
  rw [h_cong]
  -- Step 3: apply list_level_leibniz_general
  rw [list_level_leibniz_general k l (asListCochain n k α)
        (asListCochain n l β) (kSubset n (k+l+1) τ.val)]
  -- Step 4: convert the correction (last term) back to Fin form
  congr 1
  -- Last term: cupList k l α' β' (τ_list.eraseIdx k)
  --          = cupOnList n k l α β (τ_list.eraseIdx k)
  --          = cup n k l α β (faceIdx n (k+l+1) k h_k τ)
  rw [← cupOnList_eq_cupList n k l α β]
  rw [← cup_at_faceIdx_eq_cupOnList_eraseIdx n k l k
        (Nat.lt_succ_of_le (Nat.le_add_right k l)) α β τ]

end E213.Lib.Math.Cohomology.Cup.LeibnizFinGeneral
