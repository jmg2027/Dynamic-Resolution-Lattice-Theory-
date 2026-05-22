import E213.Lib.Math.Cohomology.Cup.LeibnizFinGeneral
import E213.Lib.Math.Cohomology.Cup.SubsetIdxRoundtripGeneral

/-!
# Cohomology.Cup.LeibnizFinPureForm

**Pure Fin-index form of the ∀(n, k, l) twisted Leibniz.**

Restates `fin_level_leibniz_general` with the two side terms
expressed as explicit `(delta α) (Fin idx) && β (Fin idx)` and
`α (Fin idx) && (delta β) (Fin idx)` — avoiding the `cupList`+
`deltaListR` wrapping by directly computing the Fin colex indices
of `(kSubset n (k+l+1) τ.val).take/drop` sub-lists.

PURE.
-/

namespace E213.Lib.Math.Cohomology.Cup.LeibnizFinPureForm

open E213.Lib.Math.Cohomology.Cochain.Core (Cochain)
open E213.Lib.Math.Cohomology.Cup.Core (cup)
open E213.Lib.Math.Cohomology.Delta.Core (delta subsetIdx)
open E213.Lib.Math.Cohomology.Examples.SimplexBasis (kSubset)
open E213.Lib.Math.Cohomology.Cup.FaceIdxGeneral (faceIdx)
open E213.Lib.Math.Cohomology.Cup.FinBridgeGeneral
  (kSubset_take_eq kSubset_drop_eq)
open E213.Lib.Math.Cohomology.Cup.KSubsetStructural
  (nat_add_sub_cancel)
open E213.Lib.Math.Cohomology.Cup.SubsetIdxRoundtrip (roundtrip_n_k)
open E213.Lib.Math.Cohomology.Cup.LeibnizFinGeneral
  (asListCochain fin_level_leibniz_general)
open E213.Lib.Math.Cohomology.Cup.LeibnizLexListLevel
  (cupList deltaListR)
open E213.Lib.Math.Cohomology.Cup.DeltaUnfoldGeneral (delta_eq_xorRange)
open E213.Lib.Physics.Simplex.Counts (binom)

/-! ## §1.  Take/drop Fin index helpers -/

/-- ★ Colex index of the front `m`-prefix of the (k+l+1)-subset τ.
    Valid when `m ≤ k+l+1`.  PURE. -/
def takeIdxNat (n k l m : Nat) (τ_idx : Nat) : Nat :=
  subsetIdx n m ((kSubset n (k + l + 1) τ_idx).take m)

/-- ★ Colex index of the back `(k+l+1-m)`-suffix.  PURE. -/
def dropIdxNat (n k l m : Nat) (τ_idx : Nat) : Nat :=
  subsetIdx n (k + l + 1 - m) ((kSubset n (k + l + 1) τ_idx).drop m)

/-- `takeIdxNat` is bounded: `< binom n m` when `m ≤ k+l+1` and
    `τ_idx < binom n (k+l+1)`.  PURE — composes `kSubset_take_eq` +
    `roundtrip_n_k`. -/
theorem takeIdxNat_lt (n k l m : Nat) (h_m : m ≤ k + l + 1)
    (τ_idx : Nat) (h_τ : τ_idx < binom n (k + l + 1)) :
    takeIdxNat n k l m τ_idx < binom n m := by
  obtain ⟨j_a, h_ja, h_eq⟩ :=
    kSubset_take_eq n (k + l + 1) m h_m τ_idx h_τ
  show subsetIdx n m ((kSubset n (k + l + 1) τ_idx).take m) < binom n m
  rw [h_eq, roundtrip_n_k n m j_a h_ja]
  exact h_ja

/-- `dropIdxNat` is bounded.  PURE — composes `kSubset_drop_eq` +
    `roundtrip_n_k`. -/
theorem dropIdxNat_lt (n k l m : Nat) (h_m : m ≤ k + l + 1)
    (τ_idx : Nat) (h_τ : τ_idx < binom n (k + l + 1)) :
    dropIdxNat n k l m τ_idx < binom n (k + l + 1 - m) := by
  obtain ⟨j_b, h_jb, h_eq⟩ :=
    kSubset_drop_eq n (k + l + 1) m h_m τ_idx h_τ
  show subsetIdx n (k + l + 1 - m)
       ((kSubset n (k + l + 1) τ_idx).drop m) < binom n (k + l + 1 - m)
  rw [h_eq, roundtrip_n_k n (k + l + 1 - m) j_b h_jb]
  exact h_jb

/-! ## §2.  `asListCochain` round-trip on a kSubset list -/

/-- ★ **asListCochain on a kSubset equals the Fin cochain** —
    when wrapping `α : Cochain n k` via `asListCochain` and evaluating
    at `kSubset n k j` (for valid `j < binom n k`), we recover `α ⟨j, h⟩`.
    PURE. -/
theorem asListCochain_kSubset (n k j : Nat) (h_j : j < binom n k)
    (α : Cochain n k) :
    asListCochain n k α (kSubset n k j) = α ⟨j, h_j⟩ := by
  unfold asListCochain
  have h_round : subsetIdx n k (kSubset n k j) = j :=
    roundtrip_n_k n k j h_j
  have h_in : subsetIdx n k (kSubset n k j) < binom n k :=
    h_round.symm ▸ h_j
  show (if h : subsetIdx n k (kSubset n k j) < binom n k
        then α ⟨_, h⟩ else false)
     = α ⟨j, h_j⟩
  rw [dif_pos h_in]
  apply congrArg α
  exact Fin.ext h_round

/-- ★★ **The take of a kSubset equals kSubset of its takeIdxNat** —
    bridges `kSubset_take_eq`'s existential witness to the explicit
    `takeIdxNat` definition.  PURE. -/
theorem kSubset_take_via_takeIdxNat (n k l m : Nat) (h_m : m ≤ k + l + 1)
    (τ_idx : Nat) (h_τ : τ_idx < binom n (k + l + 1)) :
    (kSubset n (k + l + 1) τ_idx).take m
    = kSubset n m (takeIdxNat n k l m τ_idx) := by
  obtain ⟨j_a, h_ja, h_eq⟩ :=
    kSubset_take_eq n (k + l + 1) m h_m τ_idx h_τ
  rw [h_eq]
  apply congrArg (kSubset n m)
  show j_a = takeIdxNat n k l m τ_idx
  show j_a = subsetIdx n m ((kSubset n (k + l + 1) τ_idx).take m)
  rw [h_eq, roundtrip_n_k n m j_a h_ja]

/-- ★★ **The drop of a kSubset equals kSubset of its dropIdxNat** —
    dual of `kSubset_take_via_takeIdxNat`.  PURE. -/
theorem kSubset_drop_via_dropIdxNat (n k l m : Nat) (h_m : m ≤ k + l + 1)
    (τ_idx : Nat) (h_τ : τ_idx < binom n (k + l + 1)) :
    (kSubset n (k + l + 1) τ_idx).drop m
    = kSubset n (k + l + 1 - m) (dropIdxNat n k l m τ_idx) := by
  obtain ⟨j_b, h_jb, h_eq⟩ :=
    kSubset_drop_eq n (k + l + 1) m h_m τ_idx h_τ
  rw [h_eq]
  apply congrArg (kSubset n (k + l + 1 - m))
  show j_b = dropIdxNat n k l m τ_idx
  show j_b = subsetIdx n (k + l + 1 - m) ((kSubset n (k + l + 1) τ_idx).drop m)
  rw [h_eq, roundtrip_n_k n (k + l + 1 - m) j_b h_jb]

/-! ## §3.  Arithmetic helpers (PURE) -/

/-- `k + l + 1 - (k + 1) = l`.  PURE — via `add_sub_add_left`. -/
theorem succ_add_sub_succ (k l : Nat) : k + l + 1 - (k + 1) = l := by
  -- k + l + 1 = k + (l + 1) defeq via Nat addition reduction
  show k + (l + 1) - (k + 1) = l
  rw [E213.Tactic.NatHelper.add_sub_add_left k (l + 1) 1]
  -- (l + 1) - 1 = l by defeq
  rfl

/-- `k + l + 1 - k = l + 1`.  PURE — via `add_sub_add_left` at m=0. -/
theorem add_succ_sub_self (k l : Nat) : k + l + 1 - k = l + 1 := by
  show k + (l + 1) - (k + 0) = l + 1
  rw [E213.Tactic.NatHelper.add_sub_add_left k (l + 1) 0]
  rfl

/-! ## §4.  deltaListR ↔ delta bridge on the kSubset list -/

/-- ★★★ **deltaListR at a kSubset = delta at the Fin index** —
    inverts `delta_eq_deltaListR` for the specific case where the
    list argument is a `kSubset`.  PURE. -/
theorem deltaListR_kSubset_eq_delta
    (n k j : Nat) (h_j : j < binom n (k + 1)) (α : Cochain n k) :
    deltaListR k (asListCochain n k α) (kSubset n (k + 1) j)
    = delta α ⟨j, h_j⟩ := by
  rw [E213.Lib.Math.Cohomology.Cup.LeibnizFinGeneral.delta_eq_deltaListR
      n k α ⟨j, h_j⟩]

/-! ## §5.  Fin-typed take/drop indices for the (k+l+1)-subset -/

/-- ★ `Fin` colex index of the front (k+1)-prefix.  PURE. -/
def kp1Fin (n k l : Nat) (τ : Fin (binom n (k + l + 1))) :
    Fin (binom n (k + 1)) :=
  ⟨takeIdxNat n k l (k + 1) τ.val,
   takeIdxNat_lt n k l (k + 1)
     (Nat.succ_le_succ (Nat.le_add_right k l)) τ.val τ.isLt⟩

/-- ★ `Fin` colex index of the back l-suffix (after drop (k+1)).  PURE. -/
def lFin (n k l : Nat) (τ : Fin (binom n (k + l + 1))) :
    Fin (binom n l) :=
  ⟨dropIdxNat n k l (k + 1) τ.val, by
    have h := dropIdxNat_lt n k l (k + 1)
      (Nat.succ_le_succ (Nat.le_add_right k l)) τ.val τ.isLt
    rw [succ_add_sub_succ k l] at h
    exact h⟩

/-- ★ `Fin` colex index of the front k-prefix.  PURE. -/
def kFin (n k l : Nat) (τ : Fin (binom n (k + l + 1))) :
    Fin (binom n k) :=
  ⟨takeIdxNat n k l k τ.val,
   takeIdxNat_lt n k l k
     (Nat.le_succ_of_le (Nat.le_add_right k l)) τ.val τ.isLt⟩

/-- ★ `Fin` colex index of the back (l+1)-suffix (after drop k).  PURE. -/
def lp1Fin (n k l : Nat) (τ : Fin (binom n (k + l + 1))) :
    Fin (binom n (l + 1)) :=
  ⟨dropIdxNat n k l k τ.val, by
    have h := dropIdxNat_lt n k l k
      (Nat.le_succ_of_le (Nat.le_add_right k l)) τ.val τ.isLt
    rw [add_succ_sub_self k l] at h
    exact h⟩

/-! ## §6.  Side-term bridges: cupList → Fin form -/

/-- ★★★ **(k+1, l) side in pure Fin form.**  PURE.  -/
theorem cupList_kp1_l_eq_fin
    (n k l : Nat) (α : Cochain n k) (β : Cochain n l)
    (τ : Fin (binom n (k + l + 1))) :
    cupList (k+1) l
      (deltaListR k (asListCochain n k α))
      (asListCochain n l β)
      (kSubset n (k + l + 1) τ.val)
    = (delta α (kp1Fin n k l τ) && β (lFin n k l τ)) := by
  have h_le : k + 1 ≤ k + l + 1 := Nat.succ_le_succ (Nat.le_add_right k l)
  unfold cupList
  rw [kSubset_take_via_takeIdxNat n k l (k+1) h_le τ.val τ.isLt]
  rw [kSubset_drop_via_dropIdxNat n k l (k+1) h_le τ.val τ.isLt]
  rw [deltaListR_kSubset_eq_delta n k (takeIdxNat n k l (k+1) τ.val)
      (kp1Fin n k l τ).isLt α]
  -- LHS now: delta α ⟨takeIdxNat ..., (kp1Fin ...).isLt⟩
  --          && asListCochain n l β (kSubset n (k+l+1-(k+1)) (dropIdxNat ...))
  have h_kSub_eq :
      kSubset n (k + l + 1 - (k + 1)) (dropIdxNat n k l (k+1) τ.val)
    = kSubset n l (dropIdxNat n k l (k+1) τ.val) :=
    congrArg (fun m => kSubset n m (dropIdxNat n k l (k+1) τ.val))
      (succ_add_sub_succ k l)
  rw [h_kSub_eq]
  rw [asListCochain_kSubset n l (dropIdxNat n k l (k+1) τ.val)
      (lFin n k l τ).isLt β]
  rfl

/-- ★★★ **(k, l+1) side in pure Fin form.**  PURE.  -/
theorem cupList_k_lp1_eq_fin
    (n k l : Nat) (α : Cochain n k) (β : Cochain n l)
    (τ : Fin (binom n (k + l + 1))) :
    cupList k (l+1)
      (asListCochain n k α)
      (deltaListR l (asListCochain n l β))
      (kSubset n (k + l + 1) τ.val)
    = (α (kFin n k l τ) && delta β (lp1Fin n k l τ)) := by
  have h_le : k ≤ k + l + 1 := Nat.le_succ_of_le (Nat.le_add_right k l)
  unfold cupList
  rw [kSubset_take_via_takeIdxNat n k l k h_le τ.val τ.isLt]
  rw [kSubset_drop_via_dropIdxNat n k l k h_le τ.val τ.isLt]
  rw [asListCochain_kSubset n k (takeIdxNat n k l k τ.val)
      (kFin n k l τ).isLt α]
  have h_kSub_eq :
      kSubset n (k + l + 1 - k) (dropIdxNat n k l k τ.val)
    = kSubset n (l + 1) (dropIdxNat n k l k τ.val) :=
    congrArg (fun m => kSubset n m (dropIdxNat n k l k τ.val))
      (add_succ_sub_self k l)
  rw [h_kSub_eq]
  rw [deltaListR_kSubset_eq_delta n l (dropIdxNat n k l k τ.val)
      (lp1Fin n k l τ).isLt β]
  rfl

/-! ## §7.  Capstone — pure Fin-index form -/

/-- ★★★★★★ **Pure Fin-index form of the ∀(n, k, l) twisted Leibniz.**

    The two side terms appear in fully Fin-typed form:
    `(delta α) (Fin idx) && β (Fin idx)` for the (k+1, l)-side and
    `α (Fin idx) && (delta β) (Fin idx)` for the (k, l+1)-side.
    No list-level wrappers in the conclusion.

    Composes `fin_level_leibniz_general` with the two side-term
    bridges `cupList_kp1_l_eq_fin` / `cupList_k_lp1_eq_fin`.  PURE. -/
theorem fin_level_leibniz_pure_form
    (n k l : Nat) (α : Cochain n k) (β : Cochain n l)
    (τ : Fin (binom n (k + l + 1))) :
    delta (cup n k l α β) τ
    = xor (xor (delta α (kp1Fin n k l τ) && β (lFin n k l τ))
               (α (kFin n k l τ) && delta β (lp1Fin n k l τ)))
          (cup n k l α β
            (faceIdx n (k+l+1) k
              (Nat.lt_succ_of_le (Nat.le_add_right k l)) τ)) := by
  rw [E213.Lib.Math.Cohomology.Cup.LeibnizFinGeneral.fin_level_leibniz_general
        n k l α β τ]
  rw [cupList_kp1_l_eq_fin n k l α β τ]
  rw [cupList_k_lp1_eq_fin n k l α β τ]

end E213.Lib.Math.Cohomology.Cup.LeibnizFinPureForm
