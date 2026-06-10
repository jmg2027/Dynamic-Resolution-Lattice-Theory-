import E213.Lib.Math.Algebra.Linalg213.Laplace
import E213.Lib.Math.Algebra.Linalg213.PermSign

/-!
# Linalg213 — the determinant of a permutation matrix is its sign

`det (permMatrix σ) = psign σ` — the **two readings of a permutation** coincide.  A
permutation `σ` (carried as its value list) has two independent numerical invariants:

  · its **sign** `psign σ` — `(−1)` to the inversion count (`Permutation.psign`);
  · the **determinant** of its permutation matrix `permMatrix σ` (a `1` in row `i`,
    column `σ i`).

This file proves they are the same integer.  The proof runs through the Leibniz form
`leibDet (permMatrix σ) = Σ_τ psign τ · Πᵢ [σ i = τ i]`: the diagonal product
`Πᵢ [σ i = τ i]` is `1` when `τ = σ` and `0` otherwise (a permutation matrix selects
exactly the permutation that built it), so the sum collapses to the single surviving
term `psign σ` — using that the enumeration `perms n` lists `σ` exactly once (nodup).
The recursive determinant follows by `Laplace.leibDet_eq_det`.

All ∅-axiom (over `Int213`).
-/

namespace E213.Lib.Math.Algebra.Linalg213.PermMatrixDet

open E213.Lib.Math.Algebra.Linalg213.DetN (det altSign)
open E213.Lib.Math.Algebra.Linalg213.Permutation
  (prodDiagFrom psign leibTerm leibDet perms iota sumZ inversions LPerm)
open E213.Lib.Math.Algebra.Linalg213.PermClosure
  (Nodup nodup_permsOf nodup_iota nodup_head_not_mem nodup_tail perm_length map_eq_of_mem
   permsOf_complete)
open E213.Lib.Math.Algebra.Linalg213.PermSign (sorted_iota sorted_imp_inv_zero)
open E213.Lib.Math.Algebra.Linalg213.Laplace (leibDet_eq_det)

/-! ## §0 — the permutation matrix -/

/-- The **permutation matrix** of a value list `σ`: a `1` in row `i` at column `σ.getD i 0`,
    `0` elsewhere.  Row `i` is the indicator of the value `σ` sends `i` to. -/
def permMatrix (σ : List Nat) : Nat → Nat → Int :=
  fun i j => if σ.getD i 0 = j then 1 else 0

/-! ## §1 — the diagonal product selects the building permutation

`prodDiagFrom (permMatrix σ) i suf` is the product of `[σ (i+k) = suf_k]` over the suffix.
It is `1` exactly when `suf` matches `σ` from offset `i`, and `0` as soon as one index
disagrees. -/

/-- All-match ⟹ the diagonal product is `1`: if `suf` agrees with `σ` from offset `i`
    at every position, every indicator factor is `1`. -/
theorem prodDiag_permMatrix_one (σ : List Nat) : ∀ (i : Nat) (suf : List Nat),
    (∀ j, j < suf.length → σ.getD (i + j) 0 = suf.getD j 0) →
    prodDiagFrom (permMatrix σ) i suf = 1
  | _, [],     _ => rfl
  | i, h :: t, hmatch => by
    show permMatrix σ i h * prodDiagFrom (permMatrix σ) (i + 1) t = 1
    have hd : σ.getD i 0 = h := hmatch 0 (Nat.succ_pos t.length)
    have hf : permMatrix σ i h = 1 := by
      show (if σ.getD i 0 = h then (1 : Int) else 0) = 1
      rw [if_pos hd]
    rw [hf, Int.one_mul]
    refine prodDiag_permMatrix_one σ (i + 1) t (fun j hj => ?_)
    have hidx : i + (j + 1) = (i + 1) + j := (Nat.add_succ i j).trans (Nat.succ_add i j).symm
    have hstep := hmatch (j + 1) (Nat.succ_lt_succ hj)
    rw [hidx] at hstep
    exact hstep

/-- A single mismatch ⟹ the diagonal product is `0`: at the first disagreeing index the
    indicator factor vanishes, zeroing the product. -/
theorem prodDiag_permMatrix_zero (σ : List Nat) : ∀ (i : Nat) (suf : List Nat) (k : Nat),
    k < suf.length → σ.getD (i + k) 0 ≠ suf.getD k 0 →
    prodDiagFrom (permMatrix σ) i suf = 0
  | _, [],     k, hk, _   => absurd hk (Nat.not_lt_zero k)
  | i, h :: t, 0, _,  hne => by
    show permMatrix σ i h * prodDiagFrom (permMatrix σ) (i + 1) t = 0
    have hd : ¬ σ.getD i 0 = h := hne
    have hf : permMatrix σ i h = 0 := by
      show (if σ.getD i 0 = h then (1 : Int) else 0) = 0
      rw [if_neg hd]
    rw [hf, E213.Meta.Int213.zero_mul]
  | i, h :: t, k + 1, hk, hne => by
    show permMatrix σ i h * prodDiagFrom (permMatrix σ) (i + 1) t = 0
    have hidx : i + (k + 1) = (i + 1) + k := (Nat.add_succ i k).trans (Nat.succ_add i k).symm
    have hrec : prodDiagFrom (permMatrix σ) (i + 1) t = 0 := by
      refine prodDiag_permMatrix_zero σ (i + 1) t k (Nat.lt_of_succ_lt_succ hk) ?_
      rw [hidx] at hne; exact hne
    rw [hrec, E213.Meta.Int213.mul_comm, E213.Meta.Int213.zero_mul]

/-- The diagonal product of `permMatrix σ` over `σ` itself is `1`. -/
theorem prodDiag_permMatrix_self (σ : List Nat) :
    prodDiagFrom (permMatrix σ) 0 σ = 1 :=
  prodDiag_permMatrix_one σ 0 σ (fun j _ => by rw [Nat.zero_add])

/-! ## §2 — index of disagreement for distinct equal-length lists -/

/-- Two distinct lists of equal length disagree at some in-range index (constructive). -/
theorem getD_ne_of_ne : ∀ (L1 L2 : List Nat), L1.length = L2.length → L1 ≠ L2 →
    ∃ k, k < L1.length ∧ L1.getD k 0 ≠ L2.getD k 0
  | [],      [],      _,  hne => absurd rfl hne
  | [],      _ :: _,  hl, _   => Nat.noConfusion hl
  | _ :: _,  [],      hl, _   => Nat.noConfusion hl
  | a :: as, b :: bs, hl, hne => by
    by_cases hab : a = b
    · have hasbs : as ≠ bs := fun e => hne (by rw [hab, e])
      rcases getD_ne_of_ne as bs (Nat.succ.inj hl) hasbs with ⟨k, hk, hkne⟩
      exact ⟨k + 1, Nat.succ_lt_succ hk, hkne⟩
    · exact ⟨0, Nat.succ_pos as.length, hab⟩

/-! ## §3 — the per-term characterization + the surviving-term sum -/

/-- For permutations `σ, p ∈ perms n`, the diagonal product of `permMatrix σ` over `p`
    is `1` if `p = σ` and `0` otherwise. -/
theorem prodDiag_permMatrix_eq_ite (n : Nat) (σ p : List Nat)
    (hσ : σ ∈ perms n) (hp : p ∈ perms n) :
    prodDiagFrom (permMatrix σ) 0 p = if p = σ then 1 else 0 := by
  by_cases hpσ : p = σ
  · rw [if_pos hpσ, hpσ]; exact prodDiag_permMatrix_self σ
  · rw [if_neg hpσ]
    have hlen : σ.length = p.length := (perm_length hσ).trans (perm_length hp).symm
    rcases getD_ne_of_ne σ p hlen (fun e => hpσ e.symm) with ⟨k, hk, hkne⟩
    exact prodDiag_permMatrix_zero σ 0 p k (hlen ▸ hk) (by rw [Nat.zero_add]; exact hkne)

/-- `a · 0 = 0` over `ℤ` (propext-free). -/
private theorem mul_zero' (a : Int) : a * 0 = 0 :=
  (E213.Meta.Int213.mul_comm a 0).trans (E213.Meta.Int213.zero_mul a)

/-- `a + 0 = a` over `ℤ` (propext-free). -/
private theorem add_zero' (a : Int) : a + 0 = a :=
  (E213.Meta.Int213.add_comm a 0).trans (E213.Meta.Int213.zero_add a)

/-- A selector sum over a list with no `a`: every indicator is `0`, so the sum is `0`. -/
theorem sumZ_select_zero (f : List Nat → Int) : ∀ (L : List (List Nat)) (a : List Nat),
    a ∉ L → sumZ (L.map (fun p => f p * (if p = a then 1 else 0))) = 0
  | [],     _, _ => rfl
  | b :: l, a, h => by
    show f b * (if b = a then 1 else 0)
          + sumZ (l.map (fun p => f p * (if p = a then 1 else 0))) = 0
    by_cases hba : b = a
    · subst hba; exact absurd (List.Mem.head l) h
    · rw [if_neg hba, mul_zero', E213.Meta.Int213.zero_add,
          sumZ_select_zero f l a (fun hm => h (List.Mem.tail b hm))]

/-- ★★ **The surviving-term sum**: in a nodup list `L` containing `a`, the selector sum
    `Σ_{p∈L} f p · [p = a]` collapses to `f a` (only the `p = a` term survives). -/
theorem sumZ_select (f : List Nat → Int) : ∀ (L : List (List Nat)),
    Nodup L → ∀ (a : List Nat), a ∈ L →
    sumZ (L.map (fun p => f p * (if p = a then 1 else 0))) = f a
  | [],     _,   _, ha => by cases ha
  | b :: l, hnd, a, ha => by
    show f b * (if b = a then 1 else 0)
          + sumZ (l.map (fun p => f p * (if p = a then 1 else 0))) = f a
    cases ha with
    | head =>
      rw [if_pos rfl, E213.Meta.Int213.mul_one,
          sumZ_select_zero f l b (nodup_head_not_mem hnd), add_zero']
    | tail _ hal =>
      by_cases hba : b = a
      · subst hba; exact absurd hal (nodup_head_not_mem hnd)
      · rw [if_neg hba, mul_zero', E213.Meta.Int213.zero_add,
            sumZ_select f l (nodup_tail hnd) a hal]

/-! ## §4 — the theorem -/

/-- ★★★ **Leibniz determinant of a permutation matrix is its sign**
    (`leibDet (permMatrix σ) = psign σ`), for `σ ∈ perms n`. -/
theorem leibDet_permMatrix (n : Nat) (σ : List Nat) (hσ : σ ∈ perms n) :
    leibDet n (permMatrix σ) = psign σ := by
  show sumZ ((perms n).map (leibTerm (permMatrix σ))) = psign σ
  rw [map_eq_of_mem (leibTerm (permMatrix σ))
        (fun p => psign p * (if p = σ then 1 else 0))
        (fun p hp => by
          show psign p * prodDiagFrom (permMatrix σ) 0 p = psign p * (if p = σ then 1 else 0)
          rw [prodDiag_permMatrix_eq_ite n σ p hσ hp])]
  exact sumZ_select psign (perms n) (nodup_permsOf (nodup_iota n)) σ hσ

/-- ★★★ **Determinant of a permutation matrix is its sign**: `det (permMatrix σ) = psign σ`
    for `σ ∈ perms n` — the sign reading and the determinant reading of a permutation agree. -/
theorem det_permMatrix (n : Nat) (σ : List Nat) (hσ : σ ∈ perms n) :
    det n (permMatrix σ) = psign σ := by
  rw [← leibDet_eq_det]
  exact leibDet_permMatrix n σ hσ

/-! ## §5 — sanity: the identity permutation matrix has determinant `1` -/

/-- `permMatrix (iota n)` is the identity matrix; its determinant is `psign (iota n) = 1`. -/
theorem det_permMatrix_iota (n : Nat) : det n (permMatrix (iota n)) = 1 := by
  rw [det_permMatrix n (iota n) (permsOf_complete (iota n) (iota n) (LPerm.refl (iota n)))]
  show altSign (inversions (iota n)) = 1
  rw [sorted_imp_inv_zero (iota n) (sorted_iota n)]; rfl

end E213.Lib.Math.Algebra.Linalg213.PermMatrixDet
