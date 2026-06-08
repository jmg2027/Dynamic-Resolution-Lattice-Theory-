import E213.Lib.Math.Algebra.Linalg213.Laplace
import E213.Lib.Math.Algebra.Linalg213.PermSign
import E213.Lib.Math.Algebra.Linalg213.ProdLperm

/-!
# Linalg213 — the transpose determinant `det Mᵀ = det M`

The classical Leibniz proof that the determinant is transpose-invariant, the payoff of
sign-multiplicativity (`PermSign.psign_mul`), ∅-axiom from scratch.

§1 — the permutation **inverse** `invPerm σ` is again a permutation (`invPerm_mem_perms`).
§2 — its sign equals `σ`'s: ★ `psign_inv` (`psign (σ⁻¹) = psign σ`), a one-liner from `psign_mul`
(`psign σ · psign σ⁻¹ = psign (σ ∘ σ⁻¹) = psign (iota n) = 1` in `{±1}`).
§3 — `invPerm` is an involution, so `perms n` is its own image under it (`perms_closed_invPerm`,
the sum-reindex).
§4 — the product-reindex `∏ᵢ Mᵀ(i,σᵢ) = ∏ⱼ M(j,σ⁻¹ⱼ)` (`prodDiag_transpose_eq`, the two factor
lists are one multiset reordered by `σ`).
§5 — assembling these: each `leibTerm Mᵀ σ = leibTerm M σ⁻¹`, so the Leibniz sum is its own
inverse-reindex — ★★★ `det_transpose` (`det Mᵀ = det M`, via `Laplace.leibDet_eq_det`).
-/

namespace E213.Lib.Math.Algebra.Linalg213.DetTranspose

open E213.Lib.Math.Algebra.Linalg213.Permutation
  (psign iota perms LPerm prodDiagFrom leibTerm leibDet sumZ map_lperm sumZ_lperm)
open E213.Lib.Math.Algebra.Linalg213.ProdLperm (prodZ prodZ_lperm)
open E213.Lib.Math.Algebra.Linalg213.PermGroup
  (composeList invPerm invPerm_getD invPerm_length idxOf idxOf_getD idxOf_lt idxOf_getD_self
   composeList_invPerm_right)
open E213.Lib.Math.Algebra.Linalg213.PermSign
  (perms_inj perms_entry_lt psign_mul altSign_self sorted_imp_inv_zero sorted_iota)
open E213.Lib.Math.Algebra.Linalg213.DetN (altSign)
open E213.Lib.Math.Algebra.Linalg213.Permutation (inversions)
open E213.Tactic.List213 (list_ext_getD getD_ge getD_map_ib length_map)
open E213.Lib.Math.Algebra.Linalg213.PermGroup (getD_iota length_iota composeList_getD composeList_length)
open E213.Lib.Math.Algebra.Linalg213.PermClosure
  (Nodup nodup_iota nodup_cons nodup_tail nodup_head_not_mem nodup_permsOf mem_map' mem_map_mpr
   permsOf_sound permsOf_complete perm_length lt_of_mem_iota)
open E213.Lib.Math.Algebra.Linalg213.Laplace (lperm_of_nodup_mem_iff mem_iota_of_lt leibDet_eq_det)
open E213.Lib.Math.Algebra.Linalg213.PermClosure (map_eq_of_mem map_map')
open E213.Lib.Math.Algebra.Linalg213.DetN (det)

/-! ## §1 — `invPerm σ` is a permutation -/

/-- `Nodup`-preservation for a map injective **on the list's elements** (cnt-based `Nodup`). -/
theorem nodup_map_restrict {α β : Type} [DecidableEq α] [DecidableEq β] {f : α → β} :
    ∀ {L : List α}, (∀ x ∈ L, ∀ y ∈ L, f x = f y → x = y) → Nodup L → Nodup (L.map f)
  | [],     _,  _  => fun _ => Nat.zero_le _
  | b :: l, hf, hL => by
    refine nodup_cons (fun hm => ?_) (nodup_map_restrict
      (fun x hx y hy => hf x (List.Mem.tail _ hx) y (List.Mem.tail _ hy)) (nodup_tail hL))
    rcases mem_map' f hm with ⟨c, hc, hfc⟩
    exact nodup_head_not_mem hL
      (hf b (List.Mem.head _) c (List.Mem.tail _ hc) hfc.symm ▸ hc)

/-- Every value `< |σ|` occurs in a permutation `σ` of `iota n`. -/
theorem perms_contains {n : Nat} {σ : List Nat} (hσ : σ ∈ perms n) {j : Nat} (hj : j < σ.length) :
    j ∈ σ :=
  PermClosure.LPerm.mem (Permutation.LPerm.symm (permsOf_sound (iota n) σ hσ))
    (mem_iota_of_lt (Nat.lt_of_lt_of_le hj (Nat.le_of_eq (perm_length hσ))))

/-- ★ **The inverse of a permutation is a permutation**: `invPerm σ ∈ perms n`. -/
theorem invPerm_mem_perms (n : Nat) (σ : List Nat) (hσ : σ ∈ perms n) : invPerm σ ∈ perms n := by
  have hlen : σ.length = n := perm_length hσ
  refine permsOf_complete (iota n) (invPerm σ) (lperm_of_nodup_mem_iff ?_ (nodup_iota n) ?_)
  · -- Nodup (invPerm σ)
    show Nodup ((iota σ.length).map (fun j => idxOf j σ))
    refine nodup_map_restrict (fun j hj j' hj' he => ?_) (nodup_iota σ.length)
    have hjσ : j ∈ σ := perms_contains hσ (lt_of_mem_iota hj)
    have hj'σ : j' ∈ σ := perms_contains hσ (lt_of_mem_iota hj')
    rw [← idxOf_getD j σ hjσ, ← idxOf_getD j' σ hj'σ, he]
  · -- mem-iff
    intro q
    constructor
    · intro hq
      rcases mem_map' _ hq with ⟨j, hj, he⟩
      exact mem_iota_of_lt (hlen ▸ he ▸ idxOf_lt j σ (perms_contains hσ (lt_of_mem_iota hj)))
    · intro hq
      have hqn : q < n := lt_of_mem_iota hq
      have hqσ : q < σ.length := Nat.lt_of_lt_of_le hqn (Nat.le_of_eq hlen.symm)
      have hself : idxOf (σ.getD q 0) σ = q :=
        PermGroup.idxOf_getD_self σ (fun a b ha hb => perms_inj hσ (hlen ▸ ha) (hlen ▸ hb)) q hqσ
      rw [← hself]
      exact mem_map_mpr (fun j => idxOf j σ)
        (mem_iota_of_lt (Nat.lt_of_lt_of_le (perms_entry_lt hσ hqn) (Nat.le_of_eq hlen.symm)))

/-! ## §2 — the sign of the inverse -/

/-- `psign (iota m) = 1` (the identity permutation is even). -/
theorem psign_iota (m : Nat) : psign (iota m) = 1 := by
  show altSign (inversions (iota m)) = 1
  rw [sorted_imp_inv_zero (iota m) (sorted_iota m)]; rfl

/-- ★★★ **The sign of the inverse permutation equals the sign**: `psign (σ⁻¹) = psign σ`.
    A one-liner from `psign_mul`: `psign σ · psign σ⁻¹ = psign (σ ∘ σ⁻¹) = psign (iota n) = 1`
    in `{±1}`, and `psign σ · psign σ = 1`, so the two signs agree. -/
theorem psign_inv (n : Nat) (σ : List Nat) (hσ : σ ∈ perms n) : psign (invPerm σ) = psign σ := by
  have hmul := psign_mul n σ (invPerm σ) hσ (invPerm_mem_perms n σ hσ)
  rw [composeList_invPerm_right σ (fun j hj => perms_contains hσ hj), psign_iota] at hmul
  have hsq : psign σ * psign σ = 1 := altSign_self (inversions σ)
  calc psign (invPerm σ)
      = psign (invPerm σ) * (psign σ * psign σ) := by rw [hsq, E213.Meta.Int213.mul_one]
    _ = (psign σ * psign (invPerm σ)) * psign σ := by ring_intZ
    _ = 1 * psign σ := by rw [← hmul]
    _ = psign σ := by ring_intZ

/-! ## §3 — `invPerm` is an involution; `perms` is closed under it -/

/-- Injectivity hypothesis for `idxOf_getD_self`, packaged from `perms`-membership. -/
private theorem inj_of_perms {n : Nat} {σ : List Nat} (hσ : σ ∈ perms n) :
    ∀ a b, a < σ.length → b < σ.length → σ.getD a 0 = σ.getD b 0 → a = b :=
  fun a b ha hb => perms_inj hσ (perm_length hσ ▸ ha) (perm_length hσ ▸ hb)

/-- ★★ **`invPerm` is an involution** on permutations of `iota n`: `(σ⁻¹)⁻¹ = σ`. -/
theorem invPerm_invol (n : Nat) (σ : List Nat) (hσ : σ ∈ perms n) : invPerm (invPerm σ) = σ := by
  have hlen : σ.length = n := perm_length hσ
  have hinv : invPerm σ ∈ perms n := invPerm_mem_perms n σ hσ
  have hilen : (invPerm σ).length = n := perm_length hinv
  refine list_ext_getD 0 ((invPerm_length (invPerm σ)).trans ((invPerm_length σ).trans hlen) |>.trans
    hlen.symm) (fun i => ?_)
  by_cases hi : i < n
  · have hm : σ.getD i 0 < n := perms_entry_lt hσ hi
    have h1 : (invPerm σ).getD (σ.getD i 0) 0 = i := by
      rw [invPerm_getD σ (σ.getD i 0) (hlen ▸ hm)]
      exact idxOf_getD_self σ (inj_of_perms hσ) i (hlen ▸ hi)
    have h2 := idxOf_getD_self (invPerm σ) (inj_of_perms hinv) (σ.getD i 0) (hilen ▸ hm)
    rw [h1] at h2
    rw [invPerm_getD (invPerm σ) i (hilen ▸ hi)]
    exact h2
  · rw [getD_ge 0 (l := invPerm (invPerm σ))
          (by rw [invPerm_length, invPerm_length]; exact Nat.not_lt.mp (hlen ▸ hi)),
        getD_ge 0 (Nat.not_lt.mp (hlen ▸ hi))]

/-- ★★ **`perms n` is closed under `invPerm`** (up to `LPerm`): `invPerm` is a bijection of the
    enumeration `perms n` onto itself (it is an involution), so reindexing the Leibniz sum by it
    leaves the sum unchanged. -/
theorem perms_closed_invPerm (n : Nat) : LPerm ((perms n).map invPerm) (perms n) := by
  apply lperm_of_nodup_mem_iff
  · refine nodup_map_restrict (L := perms n) (fun σ hσ τ hτ he => ?_) (nodup_permsOf (nodup_iota n))
    rw [← invPerm_invol n σ hσ, ← invPerm_invol n τ hτ, he]
  · exact nodup_permsOf (nodup_iota n)
  · intro q
    constructor
    · intro hq
      rcases mem_map' _ hq with ⟨σ, hσ, he⟩
      exact he ▸ invPerm_mem_perms n σ hσ
    · intro hq
      rw [← invPerm_invol n q hq]
      exact mem_map_mpr invPerm (invPerm_mem_perms n q hq)

/-! ## §4 — the product-reindex `∏ Mᵀ(k,σₖ) = ∏ M(j,σ⁻¹ⱼ)` -/

/-- The transpose matrix `Mᵀ i j = M j i`. -/
def transpose (M : Nat → Nat → Int) : Nat → Nat → Int := fun i j => M j i

/-- The diagonal-product factor list (`prodDiagFrom` as a `prodZ`). -/
def zipDiag (M : Nat → Nat → Int) : Nat → List Nat → List Int
  | _, []      => []
  | i, a :: ps => M i a :: zipDiag M (i + 1) ps

theorem prodDiagFrom_eq_prodZ (M : Nat → Nat → Int) : ∀ (i : Nat) (p : List Nat),
    prodDiagFrom M i p = prodZ (zipDiag M i p)
  | _, []      => rfl
  | i, a :: ps => by
    show M i a * prodDiagFrom M (i + 1) ps = M i a * prodZ (zipDiag M (i + 1) ps)
    rw [prodDiagFrom_eq_prodZ M (i + 1) ps]

theorem zipDiag_length (M : Nat → Nat → Int) : ∀ (i : Nat) (p : List Nat),
    (zipDiag M i p).length = p.length
  | _, []      => rfl
  | i, a :: ps => by
    show (zipDiag M (i + 1) ps).length + 1 = ps.length + 1
    rw [zipDiag_length M (i + 1) ps]

theorem zipDiag_getD (M : Nat → Nat → Int) : ∀ (i : Nat) (p : List Nat) (k : Nat), k < p.length →
    (zipDiag M i p).getD k 0 = M (i + k) (p.getD k 0)
  | i, a :: _,  0,     _ => by show M i a = M (i + 0) a; rw [Nat.add_zero]
  | i, a :: ps, k + 1, h => by
    show (zipDiag M (i + 1) ps).getD k 0 = M (i + (k + 1)) (ps.getD k 0)
    rw [zipDiag_getD M (i + 1) ps k (Nat.lt_of_succ_lt_succ h)]
    show M (i + 1 + k) (ps.getD k 0) = M (i + (k + 1)) (ps.getD k 0)
    rw [Nat.add_assoc, Nat.add_comm 1 k]

/-- A list equals the map of its own `getD` over the index range. -/
theorem list_self_map_getD (L : List Int) : L = (iota L.length).map (fun i => L.getD i 0) := by
  refine list_ext_getD 0 (by rw [length_map, length_iota]) (fun i => ?_)
  by_cases hi : i < L.length
  · rw [getD_map_ib (fun i => L.getD i 0) 0 0 (iota L.length) i (by rw [length_iota]; exact hi),
        getD_iota L.length i hi]
  · rw [getD_ge 0 (Nat.not_lt.mp hi),
        getD_ge 0 (l := (iota L.length).map (fun i => L.getD i 0))
          (by rw [length_map, length_iota]; exact Nat.not_lt.mp hi)]

/-- ★★★ **The transpose product-reindex**: `∏ᵢ Mᵀ(i,σᵢ) = ∏ⱼ M(j,σ⁻¹ⱼ)` for `σ ∈ perms n`.
    Both are `prodZ` of the same multiset of factors `{M (σₖ) k}`, reordered by the permutation `σ`
    (`composeList second σ`, which is `LPerm`-equal to `second` by `map_lperm`). -/
theorem prodDiag_transpose_eq (M : Nat → Nat → Int) (n : Nat) (σ : List Nat) (hσ : σ ∈ perms n) :
    prodDiagFrom (transpose M) 0 σ = prodDiagFrom M 0 (invPerm σ) := by
  have hlen : σ.length = n := perm_length hσ
  have hseclen : (zipDiag M 0 (invPerm σ)).length = n := by
    rw [zipDiag_length, invPerm_length, hlen]
  -- the transpose factor list = the M factor list reordered by σ
  have hkey : zipDiag (transpose M) 0 σ
      = σ.map (fun v => (zipDiag M 0 (invPerm σ)).getD v 0) := by
    refine list_ext_getD 0
      ((zipDiag_length (transpose M) 0 σ).trans (length_map σ _).symm) (fun k => ?_)
    by_cases hk : k < σ.length
    · have hsk : σ.getD k 0 < n := perms_entry_lt hσ (hlen ▸ hk)
      rw [zipDiag_getD (transpose M) 0 σ k hk,
          getD_map_ib (fun v => (zipDiag M 0 (invPerm σ)).getD v 0) 0 0 σ k hk,
          zipDiag_getD M 0 (invPerm σ) (σ.getD k 0) (by rw [invPerm_length]; exact hlen ▸ hsk),
          invPerm_getD σ (σ.getD k 0) (hlen ▸ hsk),
          idxOf_getD_self σ (inj_of_perms hσ) k hk]
      show M (σ.getD k 0) (0 + k) = M (0 + σ.getD k 0) k
      rw [Nat.zero_add, Nat.zero_add]
    · rw [getD_ge 0 (l := zipDiag (transpose M) 0 σ)
            (by rw [zipDiag_length]; exact Nat.not_lt.mp hk),
          getD_ge 0 (l := σ.map (fun v => (zipDiag M 0 (invPerm σ)).getD v 0))
            (by rw [length_map]; exact Nat.not_lt.mp hk)]
  -- the reindexed factor list is LPerm to the original (reorder by the permutation σ)
  have hlp : LPerm (σ.map (fun v => (zipDiag M 0 (invPerm σ)).getD v 0)) (zipDiag M 0 (invPerm σ)) := by
    have hrec : (iota n).map (fun v => (zipDiag M 0 (invPerm σ)).getD v 0)
        = zipDiag M 0 (invPerm σ) := (hseclen ▸ list_self_map_getD (zipDiag M 0 (invPerm σ))).symm
    have hml := map_lperm (fun v => (zipDiag M 0 (invPerm σ)).getD v 0) (permsOf_sound (iota n) σ hσ)
    rwa [hrec] at hml
  rw [prodDiagFrom_eq_prodZ (transpose M) 0 σ, hkey, prodDiagFrom_eq_prodZ M 0 (invPerm σ)]
  exact prodZ_lperm hlp

/-! ## §5 — the transpose determinant -/

/-- The Leibniz determinant is transpose-invariant: `leibDet n Mᵀ = leibDet n M`.  Each term
    reindexes by `invPerm` — `leibTerm Mᵀ σ = psign σ · ∏ Mᵀ(i,σ i) = psign(σ⁻¹)·∏ M(i,σ⁻¹ i)
    = leibTerm M σ⁻¹` (`prodDiag_transpose_eq` + `psign_inv`) — and `perms` is closed under
    `invPerm` (`perms_closed_invPerm`), so the sum is unchanged. -/
theorem leibDet_transpose (n : Nat) (M : Nat → Nat → Int) :
    leibDet n (transpose M) = leibDet n M := by
  show sumZ ((perms n).map (leibTerm (transpose M))) = sumZ ((perms n).map (leibTerm M))
  rw [map_eq_of_mem (leibTerm (transpose M)) (fun σ => leibTerm M (invPerm σ))
        (fun σ hσ => by
          show psign σ * prodDiagFrom (transpose M) 0 σ
             = psign (invPerm σ) * prodDiagFrom M 0 (invPerm σ)
          rw [prodDiag_transpose_eq M n σ hσ, psign_inv n σ hσ]),
      ← map_map' invPerm (leibTerm M) (perms n)]
  exact sumZ_lperm (map_lperm (leibTerm M) (perms_closed_invPerm n))

/-- ★★★ **The transpose determinant**: `det n Mᵀ = det n M`.  The classical Leibniz proof —
    reindex the permutation sum by the inverse (`perms_closed_invPerm`), `psign(σ⁻¹) = psign σ`
    (`psign_inv`), and the product-reindex (`prodDiag_transpose_eq`) — entirely ∅-axiom. -/
theorem det_transpose (n : Nat) (M : Nat → Nat → Int) : det n (transpose M) = det n M := by
  rw [← leibDet_eq_det n (transpose M), ← leibDet_eq_det n M, leibDet_transpose]

end E213.Lib.Math.Algebra.Linalg213.DetTranspose
