import E213.Lib.Math.Algebra.Linalg213.DetTranspose
import E213.Lib.Math.Algebra.Linalg213.CayleyHamilton

/-!
# Linalg213 — the multiplicative determinant `det (M·N) = det M · det N`

The last big determinant capstone, on the `psign_mul` keystone.  This file builds it in phases:
**§1** the symmetric-group closure `composeList α β ∈ perms n` (composition of permutations is a
permutation) and the right-translation bijection of `perms n`; **§2** the **row-permutation
determinant** `leibDet (rowPerm σ B) = psign σ · leibDet B`; (later) the function-sum expansion and
the assembly.  All ∅-axiom.
-/

namespace E213.Lib.Math.Algebra.Linalg213.DetMul

open E213.Lib.Math.Algebra.Linalg213.Permutation
  (psign iota perms LPerm prodDiagFrom leibTerm leibDet sumZ map_lperm sumZ_lperm inversions)
open E213.Lib.Math.Algebra.Linalg213.ProdLperm (prodZ prodZ_lperm)
open E213.Lib.Math.Algebra.Linalg213.PermGroup
  (composeList composeList_getD composeList_length invPerm invPerm_getD invPerm_length
   idxOf idxOf_getD idxOf_getD_self idxOf_lt)
open E213.Lib.Math.Algebra.Linalg213.PermSign (perms_inj perms_entry_lt)
open E213.Lib.Math.Algebra.Linalg213.PermClosure
  (nodup_iota nodup_of_lperm nodup_permsOf mem_map' mem_map_mpr permsOf_sound permsOf_complete
   perm_length lt_of_mem_iota)
open E213.Lib.Math.Algebra.Linalg213.Laplace (lperm_of_nodup_mem_iff mem_iota_of_lt)
open E213.Lib.Math.Algebra.Linalg213.DetTranspose
  (nodup_map_restrict perms_contains invPerm_mem_perms psign_inv
   zipDiag prodDiagFrom_eq_prodZ zipDiag_getD zipDiag_length list_self_map_getD)
open E213.Lib.Math.Algebra.Linalg213.PermSign (psign_mul altSign_self)
open E213.Lib.Math.Algebra.Linalg213.PermClosure (map_eq_of_mem map_map' sumZ_map_smul leibDet_rows_eq_ne)
open E213.Lib.Math.Algebra.Linalg213.CayleyHamilton (sumZ_map_smul_right add_zero')
open E213.Lib.Math.Algebra.Linalg213.Laplace (matMul map_flatMap sumZ_flatMap sumZ_append)
open E213.Tactic.List213 (list_ext_getD getD_ge getD_map_ib length_map)

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

/-! ## §3 — the row-permutation determinant `leibDet (rowPerm σ B) = psign σ · leibDet B` -/

/-- Permute the rows of `B` by `σ`: row `i` of `rowPerm σ B` is row `σ i` of `B`. -/
def rowPerm (σ : List Nat) (B : Nat → Nat → Int) : Nat → Nat → Int := fun i k => B (σ.getD i 0) k

/-- The diagonal product of `rowPerm σ B` over `τ` reindexes to `B` over `composeList τ σ⁻¹`. -/
theorem prodDiag_rowPerm_eq (σ : List Nat) (B : Nat → Nat → Int) (n : Nat) (hσ : σ ∈ perms n)
    (τ : List Nat) (hτ : τ ∈ perms n) :
    prodDiagFrom (rowPerm σ B) 0 τ = prodDiagFrom B 0 (composeList τ (invPerm σ)) := by
  have hσlen : σ.length = n := perm_length hσ
  have hτlen : τ.length = n := perm_length hτ
  have hseclen : (zipDiag B 0 (composeList τ (invPerm σ))).length = n := by
    rw [zipDiag_length, composeList_length, invPerm_length, hσlen]
  have hkey : zipDiag (rowPerm σ B) 0 τ
      = σ.map (fun v => (zipDiag B 0 (composeList τ (invPerm σ))).getD v 0) := by
    refine list_ext_getD 0 (by rw [zipDiag_length, length_map, hτlen, hσlen]) (fun k => ?_)
    by_cases hk : k < σ.length
    · have hkn : k < n := hσlen ▸ hk
      have hsk : σ.getD k 0 < n := perms_entry_lt hσ hkn
      rw [zipDiag_getD (rowPerm σ B) 0 τ k (hτlen ▸ hkn),
          getD_map_ib (fun v => (zipDiag B 0 (composeList τ (invPerm σ))).getD v 0) 0 0 σ k hk,
          zipDiag_getD B 0 (composeList τ (invPerm σ)) (σ.getD k 0)
            (by rw [composeList_length, invPerm_length, hσlen]; exact hsk),
          composeList_getD τ (invPerm σ) (σ.getD k 0) (by rw [invPerm_length, hσlen]; exact hsk),
          invPerm_getD σ (σ.getD k 0) (hσlen ▸ hsk),
          idxOf_getD_self σ (injp hσ) k (hσlen ▸ hkn)]
      show B (σ.getD (0 + k) 0) (τ.getD k 0) = B (0 + σ.getD k 0) (τ.getD k 0)
      rw [Nat.zero_add, Nat.zero_add]
    · rw [getD_ge 0 (l := zipDiag (rowPerm σ B) 0 τ)
            (by rw [zipDiag_length]; exact hτlen ▸ hσlen ▸ Nat.not_lt.mp hk),
          getD_ge 0 (l := σ.map (fun v => (zipDiag B 0 (composeList τ (invPerm σ))).getD v 0))
            (by rw [length_map]; exact Nat.not_lt.mp hk)]
  have hlp : LPerm (σ.map (fun v => (zipDiag B 0 (composeList τ (invPerm σ))).getD v 0))
      (zipDiag B 0 (composeList τ (invPerm σ))) := by
    have hrec : (iota n).map (fun v => (zipDiag B 0 (composeList τ (invPerm σ))).getD v 0)
        = zipDiag B 0 (composeList τ (invPerm σ)) :=
      (hseclen ▸ list_self_map_getD (zipDiag B 0 (composeList τ (invPerm σ)))).symm
    have hml := map_lperm (fun v => (zipDiag B 0 (composeList τ (invPerm σ))).getD v 0)
      (permsOf_sound (iota n) σ hσ)
    rwa [hrec] at hml
  rw [prodDiagFrom_eq_prodZ (rowPerm σ B) 0 τ, hkey, prodDiagFrom_eq_prodZ B 0 (composeList τ (invPerm σ))]
  exact prodZ_lperm hlp

/-- Per-term: `leibTerm (rowPerm σ B) τ = psign σ · leibTerm B (τ ∘ σ⁻¹)`.  The product reindexes
    (`prodDiag_rowPerm_eq`) and the sign factors via `psign_mul`/`psign_inv` (`psign σ² = 1`). -/
theorem leibTerm_rowPerm (σ : List Nat) (B : Nat → Nat → Int) (n : Nat) (τ : List Nat)
    (hσ : σ ∈ perms n) (hτ : τ ∈ perms n) :
    leibTerm (rowPerm σ B) τ = psign σ * leibTerm B (composeList τ (invPerm σ)) := by
  have hsq : psign σ * psign σ = 1 := altSign_self (inversions σ)
  show psign τ * prodDiagFrom (rowPerm σ B) 0 τ
     = psign σ * (psign (composeList τ (invPerm σ)) * prodDiagFrom B 0 (composeList τ (invPerm σ)))
  rw [prodDiag_rowPerm_eq σ B n hσ τ hτ,
      psign_mul n τ (invPerm σ) hτ (invPerm_mem_perms n σ hσ), psign_inv n σ hσ,
      show psign σ * (psign τ * psign σ * prodDiagFrom B 0 (composeList τ (invPerm σ)))
         = psign τ * (psign σ * psign σ) * prodDiagFrom B 0 (composeList τ (invPerm σ)) from by
        ring_intZ,
      hsq]
  ring_intZ

/-- ★★★ **The row-permutation determinant**: permuting the rows of `B` by `σ` multiplies the
    determinant by `psign σ`.  Each `leibTerm` reindexes by right-translation `τ ↦ τ ∘ σ⁻¹`
    (`perms_closed_rightMul`), pulling out the constant `psign σ`. -/
theorem leibDet_rowPerm (σ : List Nat) (B : Nat → Nat → Int) (n : Nat) (hσ : σ ∈ perms n) :
    leibDet n (rowPerm σ B) = psign σ * leibDet n B := by
  show sumZ ((perms n).map (leibTerm (rowPerm σ B)))
     = psign σ * sumZ ((perms n).map (leibTerm B))
  rw [map_eq_of_mem (leibTerm (rowPerm σ B))
        (fun τ => psign σ * leibTerm B (composeList τ (invPerm σ)))
        (fun τ hτ => leibTerm_rowPerm σ B n τ hσ hτ),
      sumZ_map_smul (psign σ) (fun τ => leibTerm B (composeList τ (invPerm σ))) (perms n),
      ← map_map' (fun τ => composeList τ (invPerm σ)) (leibTerm B) (perms n),
      sumZ_lperm (map_lperm (leibTerm B)
        (perms_closed_rightMul n (invPerm σ) (invPerm_mem_perms n σ hσ)))]

/-! ## §4 — non-injective row-permutations vanish; the function enumeration -/

/-- ★★ **A repeated row index makes the row-permutation determinant vanish.**  If `f` sends two
    distinct positions `i ≠ j` to the same value, `rowPerm f B` has two equal rows, so its
    determinant is `0` — the term that kills non-permutation `f` in the `det(M·N)` expansion. -/
theorem leibDet_rowPerm_zero (n : Nat) (f : List Nat) (B : Nat → Nat → Int) {i j : Nat}
    (hij : i ≠ j) (hi : i < n) (hj : j < n) (he : f.getD i 0 = f.getD j 0) :
    leibDet n (rowPerm f B) = 0 :=
  leibDet_rows_eq_ne (rowPerm f B) n i j hij hi hj (fun c => by
    show B (f.getD i 0) c = B (f.getD j 0) c; rw [he])

/-- All length-`len` lists with entries drawn from `vals` (the choice/function enumeration). -/
def tuples (vals : List Nat) : Nat → List (List Nat)
  | 0       => [[]]
  | len + 1 => vals.flatMap (fun v => (tuples vals len).map (v :: ·))

/-- All functions `[n] → [n]` as length-`n` value-lists with entries `< n`. -/
def funcs (n : Nat) : List (List Nat) := tuples (iota n) n

/-! ## §5 — the product-of-sums distributivity over the function enumeration -/

/-- The choice-product for a function `f`: `prodChoice A B start σ f = ∏ₚ A (start+p) fₚ · B fₚ σₚ`. -/
def prodChoice (A B : Nat → Nat → Int) : Nat → List Nat → List Nat → Int
  | _,     [],      _       => 1
  | start, a :: ps, j :: fs => A start j * B j a * prodChoice A B (start + 1) ps fs
  | _,     _ :: _,  []      => 1

/-- ★★★ **The product-of-sums distributivity**: the diagonal product of `A·B` over `σ` expands
    into a sum over all choice functions `f`.  Induction on `σ`: the head factor
    `(A·B) start a = Σⱼ A start j · B j a` distributes (bilinearly) over the tail's choice-sum. -/
theorem prodDiag_matMul_expand (A B : Nat → Nat → Int) (m : Nat) :
    ∀ (start : Nat) (σ : List Nat),
      prodDiagFrom (matMul m A B) start σ
        = sumZ ((tuples (iota m) σ.length).map (prodChoice A B start σ))
  | start, []      => by show (1 : Int) = 1 + 0; rw [add_zero']
  | start, a :: ps => by
    show matMul m A B start a * prodDiagFrom (matMul m A B) (start + 1) ps
       = sumZ (((iota m).flatMap (fun v => (tuples (iota m) ps.length).map (v :: ·))).map
           (prodChoice A B start (a :: ps)))
    rw [prodDiag_matMul_expand A B m (start + 1) ps,
        show matMul m A B start a = sumZ ((iota m).map (fun j => A start j * B j a)) from rfl,
        sumZ_map_smul_right (sumZ ((tuples (iota m) ps.length).map (prodChoice A B (start + 1) ps)))
          (fun j => A start j * B j a) (iota m),
        map_flatMap (prodChoice A B start (a :: ps)) (fun v => (tuples (iota m) ps.length).map (v :: ·)),
        sumZ_flatMap]
    apply congrArg sumZ
    apply map_eq_of_mem
    intro v _
    rw [map_map' (v :: ·) (prodChoice A B start (a :: ps)) (tuples (iota m) ps.length)]
    show (A start v * B v a)
           * sumZ ((tuples (iota m) ps.length).map (prodChoice A B (start + 1) ps))
       = sumZ ((tuples (iota m) ps.length).map
           (fun f' => A start v * B v a * prodChoice A B (start + 1) ps f'))
    rw [sumZ_map_smul (A start v * B v a) (prodChoice A B (start + 1) ps)]

end E213.Lib.Math.Algebra.Linalg213.DetMul
