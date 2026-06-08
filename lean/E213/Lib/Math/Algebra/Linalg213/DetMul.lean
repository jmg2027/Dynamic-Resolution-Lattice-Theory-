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
  (Nodup nodup_iota nodup_of_lperm nodup_permsOf mem_map' mem_map_mpr permsOf_sound permsOf_complete
   perm_length lt_of_mem_iota)
open E213.Lib.Math.Algebra.Linalg213.Laplace (lperm_of_nodup_mem_iff mem_iota_of_lt)
open E213.Lib.Math.Algebra.Linalg213.DetTranspose
  (nodup_map_restrict perms_contains invPerm_mem_perms psign_inv
   zipDiag prodDiagFrom_eq_prodZ zipDiag_getD zipDiag_length list_self_map_getD)
open E213.Lib.Math.Algebra.Linalg213.PermSign (psign_mul altSign_self)
open E213.Lib.Math.Algebra.Linalg213.PermClosure (map_eq_of_mem map_map' sumZ_map_smul leibDet_rows_eq_ne)
open E213.Lib.Math.Algebra.Linalg213.CayleyHamilton (sumZ_map_smul_right add_zero' mul_zero' sumZ_swap)
open E213.Lib.Math.Algebra.Linalg213.PermClosure
  (eq_one_of_le_one_of_pos nodup_tail nodup_head_not_mem)
open E213.Lib.Math.Algebra.Linalg213.PermGroup (length_iota)
open E213.Lib.Math.Algebra.Linalg213.DetN (det)
open E213.Tactic.List213 (mem_filter mem_filter_of length_filter_lt_of_mem nodup_length_le_of_subset)
open E213.Lib.Math.Algebra.Linalg213.PermClosure
  (mem_flatMap' mem_flatMap_mpr nodup_cons nodup_map nodup_flatMap cnt cnt_pos_mem cnt_pos_of_mem
   cnt_eq_zero_of_not_mem lperm_of_cnt_eq cnt_lperm)
open E213.Lib.Math.Algebra.Linalg213.Laplace
  (matMul map_flatMap sumZ_flatMap sumZ_append leibDet_eq_det)
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

/-! ## §6 — factoring `prodChoice = (∏ A) · (∏ B)` -/

/-- The `B`-product of a choice `f` against `σ`: `pB B σ f = ∏ₖ B fₖ σₖ`. -/
def pB (B : Nat → Nat → Int) : List Nat → List Nat → Int
  | [],      _       => 1
  | a :: ps, j :: fs => B j a * pB B ps fs
  | _ :: _,  []      => 1

/-- `prodChoice` factors as `(∏ A start..) · (∏ B)`. -/
theorem prodChoice_eq (A B : Nat → Nat → Int) :
    ∀ (start : Nat) (σ f : List Nat), σ.length = f.length →
      prodChoice A B start σ f = prodDiagFrom A start f * pB B σ f
  | _,     [],      [],      _ => by show (1 : Int) = 1 * 1; rw [E213.Meta.Int213.mul_one]
  | start, a :: ps, j :: fs, h => by
    show A start j * B j a * prodChoice A B (start + 1) ps fs
       = (A start j * prodDiagFrom A (start + 1) fs) * (B j a * pB B ps fs)
    rw [prodChoice_eq A B (start + 1) ps fs (Nat.succ.inj h)]; ring_intZ
  | _,     [],      _ :: _,  h => Nat.noConfusion h
  | _,     _ :: _,  [],      h => Nat.noConfusion h

/-- `drop` peels the head off: `f.drop start = f[start] :: f.drop (start+1)` (in range). -/
theorem drop_cons : ∀ (f : List Nat) (start : Nat), start < f.length →
    f.drop start = f.getD start 0 :: f.drop (start + 1)
  | _ :: _, 0,     _ => rfl
  | a :: l, k + 1, h => drop_cons l k (Nat.lt_of_succ_lt_succ h)
  | [],     _,     h => absurd h (Nat.not_lt_zero _)

/-- The `B`-product is the diagonal product of the row-permuted matrix. -/
theorem prodDiag_rowPerm_eq_pB (f : List Nat) (B : Nat → Nat → Int) :
    ∀ (start : Nat) (σ : List Nat), start + σ.length = f.length →
      prodDiagFrom (rowPerm f B) start σ = pB B σ (f.drop start)
  | _,     [],      _ => rfl
  | start, a :: ps, h => by
    have hstart : start < f.length := h ▸ Nat.lt_add_of_pos_right (Nat.succ_pos _)
    rw [drop_cons f start hstart]
    show B (f.getD start 0) a * prodDiagFrom (rowPerm f B) (start + 1) ps
       = B (f.getD start 0) a * pB B ps (f.drop (start + 1))
    rw [prodDiag_rowPerm_eq_pB f B (start + 1) ps
          (by rw [Nat.add_assoc, Nat.add_comm 1 ps.length]; exact h)]

/-- ★★ **`prodChoice` splits**: `prodChoice A B 0 σ f = prodDiagFrom A 0 f · prodDiagFrom (rowPerm f B) 0 σ`. -/
theorem prodChoice_split (A B : Nat → Nat → Int) (f σ : List Nat) (h : σ.length = f.length) :
    prodChoice A B 0 σ f = prodDiagFrom A 0 f * prodDiagFrom (rowPerm f B) 0 σ := by
  have hpb : prodDiagFrom (rowPerm f B) 0 σ = pB B σ f :=
    prodDiag_rowPerm_eq_pB f B 0 σ (by rw [Nat.zero_add]; exact h)
  rw [prodChoice_eq A B 0 σ f h, hpb]

/-! ## §7 — the sum-swap: `det(A·B) = Σ_f (∏ A) · leibDet (rowPerm f B)` -/

/-- Every list in `tuples vals len` has length `len`. -/
theorem tuples_length (vals : List Nat) : ∀ (len : Nat) (f : List Nat),
    f ∈ tuples vals len → f.length = len
  | 0,       f, h => by cases h with | head => rfl | tail _ h' => nomatch h'
  | len + 1, f, h => by
    rcases mem_flatMap' _ h with ⟨v, _, hf⟩
    rcases mem_map' _ hf with ⟨g, hg, he⟩
    rw [← he, List.length_cons, tuples_length vals len g hg]

/-- ★★★ **The function-sum form of `det(A·B)`**: `leibDet (A·B) = Σ_{f∈funcs} prodDiagFrom A 0 f ·
    leibDet (rowPerm f B)`.  Each `leibTerm (A·B) σ` expands (distributivity) into a sum over `f`;
    swapping the `σ`/`f` sums (`sumZ_swap`) and factoring (`prodChoice_split`) gives the result. -/
theorem leibDet_matMul_expand (A B : Nat → Nat → Int) (n : Nat) :
    leibDet n (matMul n A B)
      = sumZ ((funcs n).map (fun f => prodDiagFrom A 0 f * leibDet n (rowPerm f B))) := by
  show sumZ ((perms n).map (leibTerm (matMul n A B))) = _
  rw [map_eq_of_mem (leibTerm (matMul n A B))
        (fun σ => sumZ ((funcs n).map (fun f => psign σ * prodChoice A B 0 σ f)))
        (fun σ hσ => by
          have hexp : prodDiagFrom (matMul n A B) 0 σ = sumZ ((funcs n).map (prodChoice A B 0 σ)) := by
            have h := prodDiag_matMul_expand A B n 0 σ; rw [perm_length hσ] at h; exact h
          show psign σ * prodDiagFrom (matMul n A B) 0 σ
             = sumZ ((funcs n).map (fun f => psign σ * prodChoice A B 0 σ f))
          rw [hexp, sumZ_map_smul (psign σ) (prodChoice A B 0 σ) (funcs n)]),
      sumZ_swap (fun σ f => psign σ * prodChoice A B 0 σ f) (perms n) (funcs n)]
  apply congrArg sumZ
  apply map_eq_of_mem
  intro f hf
  rw [map_eq_of_mem (fun σ => psign σ * prodChoice A B 0 σ f)
        (fun σ => prodDiagFrom A 0 f * leibTerm (rowPerm f B) σ)
        (fun σ hσ => by
          show psign σ * prodChoice A B 0 σ f
             = prodDiagFrom A 0 f * (psign σ * prodDiagFrom (rowPerm f B) 0 σ)
          rw [prodChoice_split A B f σ (by rw [perm_length hσ, tuples_length (iota n) n f hf])]
          ring_intZ),
      sumZ_map_smul (prodDiagFrom A 0 f) (leibTerm (rowPerm f B)) (perms n),
      show leibDet n (rowPerm f B) = sumZ ((perms n).map (leibTerm (rowPerm f B))) from rfl]

/-! ## §8 — the `funcs ↦ perms` partition and the assembly -/

/-- A sum over a list with a vanishing predicate restricts to the filtered sublist. -/
theorem sumZ_eq_filter {α : Type} (p : α → Bool) (g : α → Int) :
    ∀ (L : List α), (∀ x ∈ L, p x = false → g x = 0) →
      sumZ (L.map g) = sumZ ((L.filter p).map g)
  | [],     _ => rfl
  | a :: l, h => by
    cases hp : p a with
    | true =>
      rw [List.filter_cons_of_pos hp]
      show g a + sumZ (l.map g) = g a + sumZ ((l.filter p).map g)
      rw [sumZ_eq_filter p g l (fun x hx => h x (List.Mem.tail _ hx))]
    | false =>
      rw [List.filter_cons_of_neg (by rw [hp]; exact Bool.noConfusion)]
      show g a + sumZ (l.map g) = sumZ ((l.filter p).map g)
      rw [h a (List.Mem.head _) hp, E213.Meta.Int213.zero_add,
          sumZ_eq_filter p g l (fun x hx => h x (List.Mem.tail _ hx))]

/-- The `perms`-sum assembles to `leibDet A · leibDet B` (each permutation term is
    `prodDiagFrom A 0 f · psign f · leibDet B = leibTerm A f · leibDet B`). -/
theorem leibDet_perms_assembly (A B : Nat → Nat → Int) (n : Nat) :
    sumZ ((perms n).map (fun f => prodDiagFrom A 0 f * leibDet n (rowPerm f B)))
      = leibDet n A * leibDet n B := by
  rw [map_eq_of_mem (fun f => prodDiagFrom A 0 f * leibDet n (rowPerm f B))
        (fun f => leibTerm A f * leibDet n B)
        (fun f hf => by
          show prodDiagFrom A 0 f * leibDet n (rowPerm f B) = leibTerm A f * leibDet n B
          rw [leibDet_rowPerm f B n hf]
          show prodDiagFrom A 0 f * (psign f * leibDet n B)
             = (psign f * prodDiagFrom A 0 f) * leibDet n B
          ring_intZ),
      ← sumZ_map_smul_right (leibDet n B) (leibTerm A) (perms n),
      show leibDet n A = sumZ ((perms n).map (leibTerm A)) from rfl]

/-! ## §9 — `perms n ⊆ funcs n`, `funcs n` nodup -/

/-- Entries of a list in `tuples vals len` are drawn from `vals`. -/
theorem tuples_entries (vals : List Nat) : ∀ (len : Nat) (f : List Nat),
    f ∈ tuples vals len → ∀ x, x ∈ f → x ∈ vals
  | 0,       _, h, x, hx => by cases h with | head => nomatch hx | tail _ h' => nomatch h'
  | len + 1, _, h, x, hx => by
    rcases mem_flatMap' _ h with ⟨v, hv, hf⟩
    rcases mem_map' _ hf with ⟨g, hg, he⟩
    rw [← he] at hx
    cases hx with
    | head      => exact hv
    | tail _ hx' => exact tuples_entries vals len g hg x hx'

/-- Conversely, any list with entries in `vals` is enumerated by `tuples`. -/
theorem mem_tuples (vals : List Nat) : ∀ (f : List Nat), (∀ x, x ∈ f → x ∈ vals) →
    f ∈ tuples vals f.length
  | [],     _ => List.Mem.head _
  | a :: l, h => mem_flatMap_mpr _ (h a (List.Mem.head _))
      (mem_map_mpr (a :: ·) (mem_tuples vals l (fun x hx => h x (List.Mem.tail _ hx))))

/-- ★ **`perms n ⊆ funcs n`**: every permutation is a function. -/
theorem perms_subset_funcs (n : Nat) (f : List Nat) (hf : f ∈ perms n) : f ∈ funcs n := by
  have hm := mem_tuples (iota n) f
    (fun x hx => PermClosure.LPerm.mem (permsOf_sound (iota n) f hf) hx)
  rw [perm_length hf] at hm
  exact hm

/-- ★ **`funcs n` has no repeats** (each function once). -/
theorem nodup_funcs (n : Nat) : Nodup (funcs n) := by
  have key : ∀ (vals : List Nat), Nodup vals → ∀ len, Nodup (tuples vals len) := by
    intro vals hv len
    induction len with
    | zero => exact nodup_cons (fun h => by cases h) (fun _ => Nat.zero_le _)
    | succ len ih =>
      refine nodup_flatMap (fun v => (tuples vals len).map (v :: ·)) (fun q => q.headD 0) vals hv ?_ ?_
      · exact fun v _ => nodup_map (fun g g' he => (List.cons.inj he).2) ih
      · intro v _ q hq
        rcases mem_map' _ hq with ⟨g, _, he⟩
        exact (congrArg (fun l => l.headD 0) he).symm
  exact key (iota n) (nodup_iota n) n

/-! ## §9b — pigeonhole: a non-permutation function repeats a value -/

/-- Membership exposes a `getD` index. -/
theorem mem_getD : ∀ (l : List Nat) (v : Nat), v ∈ l → ∃ k, k < l.length ∧ l.getD k 0 = v
  | a :: l, v, h => by
    cases h with
    | head      => exact ⟨0, Nat.succ_pos _, rfl⟩
    | tail _ h' => rcases mem_getD l v h' with ⟨k, hk, he⟩; exact ⟨k + 1, Nat.succ_lt_succ hk, he⟩

/-- The first repeated value of a list (scans head-vs-tail via the **pure** `cnt`
    decision — `Nat.decEq`, no `Decidable (a ∈ l)` instance). -/
def firstDup : List Nat → Option Nat
  | []     => none
  | a :: l => if cnt a l = 0 then firstDup l else some a

/-- A `firstDup` hit exposes two distinct positions holding the repeated value. -/
theorem firstDup_some : ∀ (f : List Nat) (v : Nat), firstDup f = some v →
    ∃ i j, i < j ∧ j < f.length ∧ f.getD i 0 = v ∧ f.getD j 0 = v
  | a :: l, v, h => by
    by_cases ha : cnt a l = 0
    · rw [show firstDup (a :: l) = (if cnt a l = 0 then firstDup l else some a) from rfl,
          if_pos ha] at h
      rcases firstDup_some l v h with ⟨i, j, hij, hj, hi', hj'⟩
      exact ⟨i + 1, j + 1, Nat.succ_lt_succ hij, Nat.succ_lt_succ hj, hi', hj'⟩
    · rw [show firstDup (a :: l) = (if cnt a l = 0 then firstDup l else some a) from rfl,
          if_neg ha] at h
      have hav : a = v := Option.some.inj h
      have hmem : a ∈ l := cnt_pos_mem (by
        cases hc : cnt a l with
        | zero => exact absurd hc ha
        | succ k => exact Nat.succ_pos k)
      rcases mem_getD l a hmem with ⟨k, hk, he⟩
      exact ⟨0, k + 1, Nat.succ_pos _, Nat.succ_lt_succ hk, hav, he.trans hav⟩

/-- No `firstDup` ⟹ the list is `List.Nodup`. -/
theorem firstDup_none : ∀ (f : List Nat), firstDup f = none → f.Nodup
  | [],     _ => List.Pairwise.nil
  | a :: l, h => by
    rw [show firstDup (a :: l) = (if cnt a l = 0 then firstDup l else some a) from rfl] at h
    by_cases ha : cnt a l = 0
    · rw [if_pos ha] at h
      have hnm : a ∉ l := fun hm => Nat.lt_irrefl 0 (ha ▸ cnt_pos_of_mem hm)
      exact List.Pairwise.cons (fun a' ha' e => hnm (by rw [e]; exact ha')) (firstDup_none l h)
    · rw [if_neg ha] at h; exact Option.noConfusion h

/-- cnt-`Nodup` ⟹ `List.Nodup`; and the converse. -/
theorem listNodup_of_cntNodup : ∀ {L : List Nat}, Nodup L → L.Nodup
  | [],     _ => List.Pairwise.nil
  | _ :: _, h => List.Pairwise.cons
      (fun _ ha' heq => nodup_head_not_mem h (by rw [heq]; exact ha'))
      (listNodup_of_cntNodup (nodup_tail h))

theorem cntNodup_of_listNodup : ∀ {L : List Nat}, L.Nodup → Nodup L
  | [],     _ => fun _ => Nat.zero_le _
  | a :: _, h => by
    cases h with
    | cons hal ht => exact nodup_cons (fun hm => (hal a hm) rfl) (cntNodup_of_listNodup ht)

/-- **Pigeonhole**: a `List.Nodup` list `L1 ⊆ L2` with `|L2| ≤ |L1|` contains all of `L2`. -/
theorem mem_of_card_le {L1 L2 : List Nat} (h1 : L1.Nodup) (hsub : ∀ x, x ∈ L1 → x ∈ L2)
    (hlen : L2.length ≤ L1.length) : ∀ v, v ∈ L2 → v ∈ L1 := by
  intro v hv
  cases Nat.eq_zero_or_pos (cnt v L1) with
  | inr hpos => exact cnt_pos_mem hpos
  | inl hzero =>
    exfalso
    have hvL1 : v ∉ L1 := fun hm => Nat.lt_irrefl 0 (hzero ▸ cnt_pos_of_mem hm)
    have hsub' : ∀ x, x ∈ L1 → x ∈ L2.filter (fun a => if a = v then false else true) :=
      fun x hx => mem_filter_of (hsub x hx) (if_neg (fun (e : x = v) => hvL1 (e ▸ hx)))
    exact Nat.lt_irrefl L1.length (Nat.lt_of_le_of_lt (nodup_length_le_of_subset h1 hsub')
      (Nat.lt_of_lt_of_le (length_filter_lt_of_mem hv (if_pos rfl)) hlen))

/-- ★ **Nodup ⟹ permutation**: a nodup function `f ∈ funcs n` is a permutation (surjective by
    pigeonhole). -/
theorem nodup_imp_perm (n : Nat) (f : List Nat) (hf : f ∈ funcs n) (hfnd : Nodup f) :
    f ∈ perms n := by
  have hlen : f.length = n := tuples_length (iota n) n f hf
  have hent : ∀ x, x ∈ f → x < n := fun x hx => lt_of_mem_iota (tuples_entries (iota n) n f hf x hx)
  have hsurj : ∀ v, v ∈ iota n → v ∈ f :=
    mem_of_card_le (listNodup_of_cntNodup hfnd) (fun x hx => mem_iota_of_lt (hent x hx))
      (Nat.le_of_eq (by rw [length_iota, hlen]))
  refine permsOf_complete (iota n) f (lperm_of_cnt_eq f (iota n) (fun a => ?_))
  by_cases ha : a < n
  · rw [eq_one_of_le_one_of_pos (hfnd a) (cnt_pos_of_mem (hsurj a (mem_iota_of_lt ha))),
        eq_one_of_le_one_of_pos (nodup_iota n a) (cnt_pos_of_mem (mem_iota_of_lt ha))]
  · rw [cnt_eq_zero_of_not_mem (fun hm => ha (hent a hm)),
        cnt_eq_zero_of_not_mem (fun hm => ha (lt_of_mem_iota hm))]

/-! ## §9c — the partition and the multiplicative determinant -/

/-- A non-permutation function repeats a value (`firstDup`), so its row-permuted determinant
    vanishes. -/
theorem term_zero_of_nonperm (A B : Nat → Nat → Int) (n : Nat) (f : List Nat) (hf : f ∈ funcs n)
    (hnp : f ∉ perms n) : prodDiagFrom A 0 f * leibDet n (rowPerm f B) = 0 := by
  have hlen : f.length = n := tuples_length (iota n) n f hf
  cases hfd : firstDup f with
  | some v =>
    rcases firstDup_some f v hfd with ⟨i, j, hij, hj, hi', hj'⟩
    rw [leibDet_rowPerm_zero n f B (Nat.ne_of_lt hij) (Nat.lt_trans hij (hlen ▸ hj)) (hlen ▸ hj)
          (hi'.trans hj'.symm), mul_zero']
  | none =>
    exact absurd (nodup_imp_perm n f hf (cntNodup_of_listNodup (firstDup_none f hfd))) hnp

/-- `cnt` under a `filter`. -/
theorem cnt_filter_le {α : Type} [DecidableEq α] (p : α → Bool) (v : α) :
    ∀ (L : List α), cnt v (L.filter p) ≤ cnt v L
  | []     => Nat.le_refl 0
  | a :: l => by
    cases hp : p a with
    | true =>
      rw [List.filter_cons_of_pos hp]
      show (if a = v then 1 else 0) + cnt v (l.filter p) ≤ (if a = v then 1 else 0) + cnt v l
      exact Nat.add_le_add_left (cnt_filter_le p v l) _
    | false =>
      rw [List.filter_cons_of_neg (by rw [hp]; exact Bool.noConfusion)]
      exact Nat.le_trans (cnt_filter_le p v l) (Nat.le_add_left _ _)

/-- `(funcs n).filter (·∈perms n)` is `LPerm` to `perms n`. -/
theorem funcs_filter_perms_lperm (n : Nat) :
    LPerm ((funcs n).filter (fun (f : List Nat) => decide (0 < cnt f (perms n)))) (perms n) := by
  apply lperm_of_nodup_mem_iff
  · exact fun v => Nat.le_trans
      (cnt_filter_le (fun (f : List Nat) => decide (0 < cnt f (perms n))) v (funcs n))
      (nodup_funcs n v)
  · exact nodup_permsOf (nodup_iota n)
  · intro q
    constructor
    · intro hq; exact cnt_pos_mem (of_decide_eq_true (mem_filter hq).2)
    · intro hq
      exact mem_filter_of (perms_subset_funcs n q hq) (decide_eq_true (cnt_pos_of_mem hq))

/-- ★★★ **The Leibniz determinant is multiplicative**: `leibDet (A·B) = leibDet A · leibDet B`. -/
theorem leibDet_matMul (A B : Nat → Nat → Int) (n : Nat) :
    leibDet n (matMul n A B) = leibDet n A * leibDet n B := by
  rw [leibDet_matMul_expand A B n,
      sumZ_eq_filter (fun (f : List Nat) => decide (0 < cnt f (perms n)))
        (fun f => prodDiagFrom A 0 f * leibDet n (rowPerm f B)) (funcs n)
        (fun f hf hd => term_zero_of_nonperm A B n f hf
          (fun hm => of_decide_eq_false hd (cnt_pos_of_mem hm))),
      sumZ_lperm (map_lperm (fun f => prodDiagFrom A 0 f * leibDet n (rowPerm f B))
        (funcs_filter_perms_lperm n)),
      leibDet_perms_assembly A B n]

/-- ★★★ **The multiplicative determinant**: `det n (A·B) = det n A · det n B`. -/
theorem det_matMul (A B : Nat → Nat → Int) (n : Nat) :
    det n (matMul n A B) = det n A * det n B := by
  rw [← leibDet_eq_det n (matMul n A B), ← leibDet_eq_det n A, ← leibDet_eq_det n B, leibDet_matMul]

end E213.Lib.Math.Algebra.Linalg213.DetMul
