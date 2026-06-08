import E213.Lib.Math.Algebra.Linalg213.DetTranspose

/-!
# Linalg213 — the multiplicative determinant `det (M·N) = det M · det N`

The last big determinant capstone, on the `psign_mul` keystone.  This file builds it in phases:
**§1** the symmetric-group closure `composeList α β ∈ perms n` (composition of permutations is a
permutation) and the right-translation bijection of `perms n`; **§2** the **row-permutation
determinant** `leibDet (rowPerm σ B) = psign σ · leibDet B`; (later) the function-sum expansion and
the assembly.  All ∅-axiom.
-/

namespace E213.Lib.Math.Algebra.Linalg213.DetMul

open E213.Lib.Math.Algebra.Linalg213.Permutation (psign iota perms LPerm)
open E213.Lib.Math.Algebra.Linalg213.PermGroup
  (composeList composeList_getD composeList_length invPerm invPerm_getD invPerm_length
   idxOf idxOf_getD idxOf_getD_self idxOf_lt)
open E213.Lib.Math.Algebra.Linalg213.PermSign (perms_inj perms_entry_lt)
open E213.Lib.Math.Algebra.Linalg213.PermClosure
  (nodup_iota nodup_of_lperm nodup_permsOf mem_map' mem_map_mpr permsOf_sound permsOf_complete
   perm_length lt_of_mem_iota)
open E213.Lib.Math.Algebra.Linalg213.Laplace (lperm_of_nodup_mem_iff mem_iota_of_lt)
open E213.Lib.Math.Algebra.Linalg213.DetTranspose
  (nodup_map_restrict perms_contains invPerm_mem_perms)
open E213.Tactic.List213 (list_ext_getD getD_ge)

/-- Position-injectivity hypothesis for `idxOf_getD_self`, from `perms`-membership. -/
private theorem injp {n : Nat} {σ : List Nat} (hσ : σ ∈ perms n) :
    ∀ a b, a < σ.length → b < σ.length → σ.getD a 0 = σ.getD b 0 → a = b :=
  fun a b ha hb => perms_inj hσ (perm_length hσ ▸ ha) (perm_length hσ ▸ hb)

/-! ## §1 — composition of permutations is a permutation -/

/-- ★★ **The symmetric group closes**: `composeList α β ∈ perms n` for `α, β ∈ perms n`. -/
theorem composeList_mem_perms (n : Nat) (α β : List Nat) (hα : α ∈ perms n) (hβ : β ∈ perms n) :
    composeList α β ∈ perms n := by
  have hαlen : α.length = n := perm_length hα
  have hβlen : β.length = n := perm_length hβ
  have hβlt : ∀ v, v ∈ β → v < n := fun v hv =>
    lt_of_mem_iota (PermClosure.LPerm.mem (permsOf_sound (iota n) β hβ) hv)
  refine permsOf_complete (iota n) (composeList α β) (lperm_of_nodup_mem_iff ?_ (nodup_iota n) ?_)
  · -- Nodup (composeList α β) = Nodup (β.map (α.getD · 0))
    refine nodup_map_restrict (fun v hv v' hv' he => ?_)
      (nodup_of_lperm (permsOf_sound (iota n) β hβ) (nodup_iota n))
    exact perms_inj hα (hαlen ▸ hβlt v hv) (hαlen ▸ hβlt v' hv') he
  · intro q
    constructor
    · intro hq
      rcases mem_map' _ hq with ⟨v, hv, he⟩
      exact mem_iota_of_lt (he ▸ perms_entry_lt hα (hβlt v hv))
    · intro hq
      have hqn : q < n := lt_of_mem_iota hq
      have hqα : q ∈ α := perms_contains hα (hαlen ▸ hqn)
      have hm : idxOf q α < n := hαlen ▸ idxOf_lt q α hqα
      have hmβ : idxOf q α ∈ β := perms_contains hβ (hβlen ▸ hm)
      rw [← idxOf_getD q α hqα]
      exact mem_map_mpr (fun v => α.getD v 0) hmβ

/-! ## §2 — right translation is a bijection of `perms n` -/

/-- `(τ ∘ ρ) ∘ ρ⁻¹ = τ` (right cancellation), by `getD`-extensionality. -/
theorem composeList_rightInv (n : Nat) (τ ρ : List Nat) (hτ : τ ∈ perms n) (hρ : ρ ∈ perms n) :
    composeList (composeList τ ρ) (invPerm ρ) = τ := by
  have hρlen : ρ.length = n := perm_length hρ
  have hτlen : τ.length = n := perm_length hτ
  refine list_ext_getD 0 (by rw [composeList_length, invPerm_length, hρlen, hτlen]) (fun k => ?_)
  by_cases hk : k < n
  · have hkρ : k ∈ ρ := perms_contains hρ (hρlen ▸ hk)
    rw [composeList_getD (composeList τ ρ) (invPerm ρ) k (by rw [invPerm_length, hρlen]; exact hk),
        invPerm_getD ρ k (hρlen ▸ hk),
        composeList_getD τ ρ (idxOf k ρ) (idxOf_lt k ρ hkρ),
        idxOf_getD k ρ hkρ]
  · rw [getD_ge 0 (l := composeList (composeList τ ρ) (invPerm ρ))
          (by rw [composeList_length, invPerm_length, hρlen]; exact Nat.not_lt.mp hk),
        getD_ge 0 (hτlen ▸ Nat.not_lt.mp hk)]

/-- `(q ∘ ρ⁻¹) ∘ ρ = q` (the other cancellation). -/
theorem composeList_leftInv (n : Nat) (q ρ : List Nat) (hq : q ∈ perms n) (hρ : ρ ∈ perms n) :
    composeList (composeList q (invPerm ρ)) ρ = q := by
  have hρlen : ρ.length = n := perm_length hρ
  have hqlen : q.length = n := perm_length hq
  have hinv : invPerm ρ ∈ perms n := invPerm_mem_perms n ρ hρ
  refine list_ext_getD 0 (by rw [composeList_length, hρlen, hqlen]) (fun k => ?_)
  by_cases hk : k < n
  · have hsk : ρ.getD k 0 < n := perms_entry_lt hρ hk
    rw [composeList_getD (composeList q (invPerm ρ)) ρ k (hρlen ▸ hk),
        composeList_getD q (invPerm ρ) (ρ.getD k 0) (by rw [invPerm_length, hρlen]; exact hsk),
        invPerm_getD ρ (ρ.getD k 0) (hρlen ▸ hsk),
        idxOf_getD_self ρ (injp hρ) k (hρlen ▸ hk)]
  · rw [getD_ge 0 (l := composeList (composeList q (invPerm ρ)) ρ)
          (by rw [composeList_length, hρlen]; exact Nat.not_lt.mp hk),
        getD_ge 0 (hqlen ▸ Nat.not_lt.mp hk)]

/-- ★★ **Right translation by `ρ` is a bijection of `perms n`** (up to `LPerm`): mapping each
    permutation to `τ ∘ ρ` permutes the enumeration. -/
theorem perms_closed_rightMul (n : Nat) (ρ : List Nat) (hρ : ρ ∈ perms n) :
    LPerm ((perms n).map (fun τ => composeList τ ρ)) (perms n) := by
  apply lperm_of_nodup_mem_iff
  · refine nodup_map_restrict (L := perms n) (fun τ hτ τ' hτ' he => ?_) (nodup_permsOf (nodup_iota n))
    rw [← composeList_rightInv n τ ρ hτ hρ, ← composeList_rightInv n τ' ρ hτ' hρ, he]
  · exact nodup_permsOf (nodup_iota n)
  · intro q
    constructor
    · intro hq
      rcases mem_map' _ hq with ⟨τ, hτ, he⟩
      exact he ▸ composeList_mem_perms n τ ρ hτ hρ
    · intro hq
      rw [← composeList_leftInv n q ρ hq hρ]
      exact mem_map_mpr (fun τ => composeList τ ρ)
        (composeList_mem_perms n q (invPerm ρ) hq (invPerm_mem_perms n ρ hρ))

end E213.Lib.Math.Algebra.Linalg213.DetMul
