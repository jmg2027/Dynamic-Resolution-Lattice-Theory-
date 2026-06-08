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
  (composeList composeList_getD composeList_length invPerm invPerm_getD idxOf idxOf_getD idxOf_lt)
open E213.Lib.Math.Algebra.Linalg213.PermSign (perms_inj perms_entry_lt)
open E213.Lib.Math.Algebra.Linalg213.PermClosure
  (nodup_iota nodup_of_lperm mem_map' mem_map_mpr permsOf_sound permsOf_complete perm_length
   lt_of_mem_iota)
open E213.Lib.Math.Algebra.Linalg213.Laplace (lperm_of_nodup_mem_iff mem_iota_of_lt)
open E213.Lib.Math.Algebra.Linalg213.DetTranspose (nodup_map_restrict perms_contains)

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

end E213.Lib.Math.Algebra.Linalg213.DetMul
