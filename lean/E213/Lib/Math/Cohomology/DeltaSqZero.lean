import E213.Lib.Math.Cohomology.Delta.Core
import E213.Lib.Math.Cohomology.Examples.ColexRoundTrip
import E213.Lib.Math.Cohomology.Examples.XorInvolution
import E213.Lib.Math.Cohomology.Delta.Pointwise

/-!
# Toward the dimension-free `δ² = 0` — `deltaAt` as a clean `xorFold`

`deltaAt`'s body is a `List.foldl` over a **dependent `if`** (the in-range guard on the
face's colex index).  To feed `δ²` into the involution engine
(`XorInvolution.xorFold_involution`), the guard must be removed.

The trick: evaluate `σ` at a `Nat` index via `cochainAtNat`, which returns `false`
out of range.  Then each `deltaAt` step is `xor acc (cochainAtNat σ faceIdx)`
**unconditionally** — in range it is the real `σ`-value; out of range
`xor acc false = acc`, exactly the `else` branch.  So `deltaAt = xorFold (…)` with no
guard, the form the involution engine consumes.

This is the first bridge lemma; the full `delta_sq_zero_general` then composes two
`deltaAt_eq_xorFold` rewrites with the reverse round-trip (`kSubset_subsetIdx`) and the
`(a,b) ↦ (b+1,a)` involution (`eraseIdx_eraseIdx_comm`).
-/

namespace E213.Lib.Math.Cohomology.DeltaSqZero

open E213.Lib.Physics.Simplex.Counts (binom)
open E213.Lib.Math.Cohomology.Cochain.Core (Cochain)
open E213.Lib.Math.Cohomology.Delta.Core (deltaAt subsetIdx delta)
open E213.Lib.Math.Cohomology.Examples.SimplexBasis (kSubset)
open E213.Lib.Math.Cohomology.Examples.XorInvolution (xorFold xorFold_involution)
open E213.Lib.Math.Cohomology.Examples.ColexRoundTrip
  (mem_range_lt range_concat eraseIdx_eraseIdx_comm kSubset_sorted kSubset_length
   kSubset_mem_lt sorted_eraseIdx mem_eraseIdx_imp_mem subsetIdx_lt kSubset_subsetIdx)
open E213.Tactic.ListHelper (length_eraseIdx_of_lt)
open E213.Tactic.List213
  (nodup_append nodup_map_of_inj mem_map_of_mem mem_append_iff exists_of_mem_map)

/-! ## Bool XOR algebra (local, propext-free) -/

private theorem xor_false (b : Bool) : xor b false = b := by cases b <;> rfl
private theorem false_xor (b : Bool) : xor false b = b := by cases b <;> rfl
private theorem xor_assoc (a b c : Bool) : xor (xor a b) c = xor a (xor b c) := by
  cases a <;> cases b <;> cases c <;> rfl

/-! ## `List.foldl xor` is `xorFold` -/

/-- Accumulator extraction for a left XOR-fold. -/
private theorem foldl_xor_acc {α : Type _} (h : α → Bool) :
    ∀ (l : List α) (init : Bool),
      l.foldl (fun acc x => xor acc (h x)) init = xor init (xorFold h l)
  | [],      init => (xor_false init).symm
  | x :: xs, init => by
    show (xs.foldl (fun acc x => xor acc (h x)) (xor init (h x)))
          = xor init (xorFold h (x :: xs))
    exact (foldl_xor_acc h xs (xor init (h x))).trans (xor_assoc init (h x) (xorFold h xs))

/-- `List.foldl (xor · (h ·)) false = xorFold h`. -/
private theorem foldl_xor_false {α : Type _} (h : α → Bool) (l : List α) :
    l.foldl (fun acc x => xor acc (h x)) false = xorFold h l :=
  (foldl_xor_acc h l false).trans (false_xor _)

/-! ## `cochainAtNat` — evaluate a cochain at a `Nat` index (false out of range) -/

/-- `σ` at a `Nat` index, `false` outside `Fin (binom n k)`.  The guard-absorbing
    evaluation: in range it is `σ ⟨idx, _⟩`; out of range it is `false`. -/
def cochainAtNat {n k : Nat} (σ : Cochain n k) (idx : Nat) : Bool :=
  if h : idx < binom n k then σ ⟨idx, h⟩ else false

/-- ★★★ **`deltaAt` is a guard-free `xorFold`.**  Reading `σ` through `cochainAtNat`
    collapses the dependent-`if` in `deltaAt` to an unconditional XOR over the faces:
    `deltaAt n k σ τ = xorFold (cochainAtNat σ ∘ faceIdx) (range (k+1))`, where
    `faceIdx i = subsetIdx n k ((kSubset n (k+1) τ).eraseIdx i)`.  ∅-axiom. -/
theorem deltaAt_eq_xorFold {n k : Nat} (σ : Cochain n k) (τ_idx : Nat) :
    deltaAt n k σ τ_idx
      = xorFold (fun i => cochainAtNat σ (subsetIdx n k ((kSubset n (k + 1) τ_idx).eraseIdx i)))
                (List.range (k + 1)) := by
  show (List.range (k + 1)).foldl
        (fun acc i =>
          if h : subsetIdx n k ((kSubset n (k + 1) τ_idx).eraseIdx i) < binom n k
          then xor acc (σ ⟨_, h⟩) else acc) false
       = xorFold _ _
  have hstep : ∀ acc i,
      (if h : subsetIdx n k ((kSubset n (k + 1) τ_idx).eraseIdx i) < binom n k
       then xor acc (σ ⟨_, h⟩) else acc)
      = xor acc (cochainAtNat σ (subsetIdx n k ((kSubset n (k + 1) τ_idx).eraseIdx i))) := by
    intro acc i
    by_cases hc : subsetIdx n k ((kSubset n (k + 1) τ_idx).eraseIdx i) < binom n k
    · have hL : (if h : subsetIdx n k ((kSubset n (k + 1) τ_idx).eraseIdx i) < binom n k
                 then xor acc (σ ⟨_, h⟩) else acc) = xor acc (σ ⟨_, hc⟩) := dif_pos hc
      have hR : cochainAtNat σ (subsetIdx n k ((kSubset n (k + 1) τ_idx).eraseIdx i))
                  = σ ⟨_, hc⟩ := dif_pos hc
      exact hL.trans (congrArg (xor acc) hR.symm)
    · have hL : (if h : subsetIdx n k ((kSubset n (k + 1) τ_idx).eraseIdx i) < binom n k
                 then xor acc (σ ⟨_, h⟩) else acc) = acc := dif_neg hc
      have hR : cochainAtNat σ (subsetIdx n k ((kSubset n (k + 1) τ_idx).eraseIdx i))
                  = false := dif_neg hc
      exact hL.trans ((xor_false acc).symm.trans (congrArg (xor acc) hR.symm))
  exact (E213.Lib.Math.Cohomology.Delta.Pointwise.foldl_step_eq _ _ hstep (List.range (k + 1)) false).trans
    (foldl_xor_false _ (List.range (k + 1)))

/-! ## `xorFold` append / map, and a range Nodup -/

private theorem xorFold_append {α : Type _} (f : α → Bool) :
    ∀ (l m : List α), xorFold f (l ++ m) = xor (xorFold f l) (xorFold f m)
  | [],      m => (false_xor _).symm
  | x :: xs, m => by
    show xor (f x) (xorFold f (xs ++ m)) = xor (xorFold f (x :: xs)) (xorFold f m)
    exact (congrArg (xor (f x)) (xorFold_append f xs m)).trans
      (xor_assoc (f x) (xorFold f xs) (xorFold f m)).symm

private theorem xorFold_map {α β : Type _} (f : β → Bool) (g : α → β) :
    ∀ (l : List α), xorFold f (l.map g) = xorFold (fun a => f (g a)) l
  | []      => rfl
  | x :: xs => congrArg (xor (f (g x))) (xorFold_map f g xs)

private theorem lt_mem_range : ∀ {q b : Nat}, b < q → b ∈ List.range q
  | q + 1, b, hb => by
    refine (range_concat q).symm ▸ ?_
    rcases Nat.lt_or_ge b q with h | h
    · exact E213.Tactic.List213.mem_append_left (lt_mem_range h)
    · have hbq : b = q := Nat.le_antisymm (Nat.le_of_lt_succ hb) h
      exact hbq ▸ E213.Tactic.ListHelper.mem_append_singleton_right (List.range q) q

private theorem range_nodup : ∀ (m : Nat), (List.range m).Nodup
  | 0     => List.Pairwise.nil
  | m + 1 =>
    (range_concat m).symm ▸ nodup_append (range_nodup m)
      (List.Pairwise.cons (fun _ hb => nomatch hb) List.Pairwise.nil)
      (fun a ha hb => by
        have hlt : a < m := mem_range_lt a m ha
        cases hb with
        | head => exact Nat.lt_irrefl m hlt
        | tail _ h => exact nomatch h)

/-! ## The `(a,b)` grid as an explicit `Nodup` list -/

/-- The `p × q` index grid `{(a,b) : a < p, b < q}` as a list (row-major). -/
def gridList : Nat → Nat → List (Nat × Nat)
  | 0,     _ => []
  | p + 1, q => gridList p q ++ (List.range q).map (fun b => (p, b))

/-- A `xorFold` over the grid is the nested `xorFold` (outer `a`, inner `b`). -/
private theorem xorFold_gridList (F : Nat × Nat → Bool) :
    ∀ (p q : Nat),
      xorFold F (gridList p q)
        = xorFold (fun a => xorFold (fun b => F (a, b)) (List.range q)) (List.range p)
  | 0,     _ => rfl
  | p + 1, q => by
    show xorFold F (gridList p q ++ (List.range q).map (fun b => (p, b)))
          = xorFold (fun a => xorFold (fun b => F (a, b)) (List.range q)) (List.range (p + 1))
    have hrow : xorFold F ((List.range q).map (fun b => (p, b)))
                  = xorFold (fun b => F (p, b)) (List.range q) :=
      xorFold_map F (fun b => (p, b)) (List.range q)
    have houter : xorFold (fun a => xorFold (fun b => F (a, b)) (List.range q)) (List.range (p + 1))
                    = xor (xorFold (fun a => xorFold (fun b => F (a, b)) (List.range q)) (List.range p))
                          (xorFold (fun b => F (p, b)) (List.range q)) := by
      have := xorFold_append (fun a => xorFold (fun b => F (a, b)) (List.range q))
                (List.range p) [p]
      exact (congrArg (xorFold _) (range_concat p)).trans
        (this.trans (congrArg (xor _) (xor_false _)))
    calc xorFold F (gridList p q ++ (List.range q).map (fun b => (p, b)))
        = xor (xorFold F (gridList p q)) (xorFold F ((List.range q).map (fun b => (p, b)))) :=
          xorFold_append F (gridList p q) _
      _ = xor (xorFold (fun a => xorFold (fun b => F (a, b)) (List.range q)) (List.range p))
              (xorFold (fun b => F (p, b)) (List.range q)) := by
          exact congrArg (fun z => xor z _) (xorFold_gridList F p q) |>.trans
            (congrArg (xor _) hrow)
      _ = _ := houter.symm

/-- Membership: `(a,b) ∈ gridList p q` iff `a < p ∧ b < q` (the directions used). -/
private theorem mem_gridList_of : ∀ {p q a b : Nat}, a < p → b < q → (a, b) ∈ gridList p q
  | p + 1, q, a, b, ha, hb => by
    show (a, b) ∈ gridList p q ++ (List.range q).map (fun b => (p, b))
    rcases Nat.lt_or_ge a p with h | h
    · exact E213.Tactic.List213.mem_append_left (mem_gridList_of h hb)
    · have hap : a = p := Nat.le_antisymm (Nat.le_of_lt_succ ha) h
      refine E213.Tactic.List213.mem_append_right _ ?_
      have : (p, b) ∈ (List.range q).map (fun b => (p, b)) :=
        mem_map_of_mem (fun b => (p, b)) (lt_mem_range hb)
      exact hap ▸ this

private theorem fst_lt_of_mem : ∀ {p q : Nat} {ab : Nat × Nat}, ab ∈ gridList p q → ab.1 < p
  | p + 1, q, ab, hmem => by
    rcases mem_append_iff hmem with h | h
    · exact Nat.lt_succ_of_lt (fst_lt_of_mem h)
    · obtain ⟨b, _, hb⟩ := exists_of_mem_map h
      exact hb ▸ Nat.lt_succ_self p

private theorem snd_lt_of_mem : ∀ {p q : Nat} {ab : Nat × Nat}, ab ∈ gridList p q → ab.2 < q
  | p + 1, q, ab, hmem => by
    rcases mem_append_iff hmem with h | h
    · exact snd_lt_of_mem h
    · obtain ⟨b, hbr, hb⟩ := exists_of_mem_map h
      exact hb ▸ mem_range_lt b q hbr

private theorem gridList_nodup : ∀ (p q : Nat), (gridList p q).Nodup
  | 0,     _ => List.Pairwise.nil
  | p + 1, q => by
    show (gridList p q ++ (List.range q).map (fun b => (p, b))).Nodup
    refine nodup_append (gridList_nodup p q) ?_ ?_
    · exact nodup_map_of_inj
        (fun a _ b _ hab => congrArg Prod.snd hab) (range_nodup q)
    · intro x hx hx'
      have h1 : x.1 < p := fst_lt_of_mem hx
      obtain ⟨b, _, hb⟩ := exists_of_mem_map hx'
      have : x.1 = p := (hb ▸ rfl : x.1 = p)
      exact Nat.lt_irrefl p (this ▸ h1)

/-! ## The grid involution and the abstract `δ²=0` cancellation -/

/-- The order-swap involution on the removal grid: `(a,b) ↦ (b+1, a)` for `a ≤ b`,
    else `(b, a-1)`.  The two members of each orbit are the two removal orders of the
    same vertex pair (`eraseIdx_eraseIdx_comm`). -/
def gridInv (ab : Nat × Nat) : Nat × Nat :=
  if ab.1 ≤ ab.2 then (ab.2 + 1, ab.1) else (ab.2, ab.1 - 1)

/-- ★★★ **Abstract `δ²=0` cancellation.**  For any list `L`, the XOR over the `(k+2)×(k+1)`
    removal grid of `σ` at the double-erase face `((L.eraseIdx a).eraseIdx b)` is `false`:
    the order-swap involution `gridInv` is fixed-point-free and preserves the summand (the
    two removal orders hit the same face, `eraseIdx_eraseIdx_comm`), so every value cancels
    in pairs (`xorFold_involution`).  This is `δ²σ(τ) = 0` once `δ²` is unfolded to this XOR. -/
theorem grid_xorFold_zero {n k : Nat} (σ : Cochain n k) (L : List Nat) :
    xorFold (fun ab : Nat × Nat =>
              cochainAtNat σ (subsetIdx n k ((L.eraseIdx ab.1).eraseIdx ab.2)))
            (gridList (k + 2) (k + 1)) = false := by
  refine xorFold_involution _ gridInv _ (gridList_nodup (k + 2) (k + 1)) ?_ ?_ ?_ ?_
  · -- closed under gridInv
    intro ab hab
    have ha : ab.1 < k + 2 := fst_lt_of_mem hab
    have hb : ab.2 < k + 1 := snd_lt_of_mem hab
    by_cases h : ab.1 ≤ ab.2
    · have hgi : gridInv ab = (ab.2 + 1, ab.1) := if_pos h
      exact hgi ▸ mem_gridList_of (Nat.succ_lt_succ hb) (Nat.lt_of_le_of_lt h hb)
    · have hgi : gridInv ab = (ab.2, ab.1 - 1) := if_neg h
      refine hgi ▸ mem_gridList_of (Nat.lt_succ_of_lt hb) ?_
      exact Nat.lt_of_le_of_lt (Nat.sub_le_sub_right (Nat.le_of_lt_succ ha) 1) (Nat.lt_succ_self k)
  · -- fixed-point-free
    intro ab hab
    by_cases h : ab.1 ≤ ab.2
    · have hgi : gridInv ab = (ab.2 + 1, ab.1) := if_pos h
      intro heq
      have e : (ab.2 + 1, ab.1) = ab := hgi.symm.trans heq
      have hf : ab.2 + 1 = ab.1 := congrArg Prod.fst e
      have hs : ab.1 = ab.2 := congrArg Prod.snd e
      exact absurd (hf.trans hs).symm (Nat.ne_of_lt (Nat.lt_succ_self ab.2))
    · have h' : ab.2 < ab.1 := Nat.lt_of_not_le h
      have hgi : gridInv ab = (ab.2, ab.1 - 1) := if_neg h
      intro heq
      have e : (ab.2, ab.1 - 1) = ab := hgi.symm.trans heq
      have hf : ab.2 = ab.1 := congrArg Prod.fst e
      exact Nat.lt_irrefl ab.1 (hf ▸ h')
  · -- involutive
    intro ab hab
    by_cases h : ab.1 ≤ ab.2
    · have hgi : gridInv ab = (ab.2 + 1, ab.1) := if_pos h
      -- inner: ¬ (ab.2+1 ≤ ab.1)  since ab.1 ≤ ab.2 < ab.2+1
      have hinner : ¬ ((ab.2 + 1 : Nat) ≤ ab.1) :=
        fun hc => Nat.lt_irrefl ab.1 (Nat.lt_of_lt_of_le (Nat.lt_succ_of_le h) hc)
      have hgi2 : gridInv (ab.2 + 1, ab.1) = (ab.1, ab.2) := by
        show (if (ab.2 + 1 : Nat) ≤ ab.1 then _ else ((ab.1, (ab.2 + 1) - 1))) = (ab.1, ab.2)
        exact (if_neg hinner).trans (congrArg (fun z => (ab.1, z)) (Nat.succ_sub_one ab.2))
      exact (congrArg gridInv hgi).trans hgi2
    · have h' : ab.2 < ab.1 := Nat.lt_of_not_le h
      have hgi : gridInv ab = (ab.2, ab.1 - 1) := if_neg h
      have hle : ab.2 ≤ ab.1 - 1 := Nat.le_sub_one_of_lt h'
      have hsucc : (ab.1 - 1) + 1 = ab.1 := Nat.succ_pred_eq_of_pos (Nat.lt_of_le_of_lt (Nat.zero_le _) h')
      have hgi2 : gridInv (ab.2, ab.1 - 1) = (ab.1, ab.2) := by
        show (if ab.2 ≤ ab.1 - 1 then ((ab.1 - 1) + 1, ab.2) else _) = (ab.1, ab.2)
        exact (if_pos hle).trans (congrArg (fun z => (z, ab.2)) hsucc)
      exact (congrArg gridInv hgi).trans hgi2
  · -- summand-preserving (the simplicial commutation)
    intro ab hab
    by_cases h : ab.1 ≤ ab.2
    · have hgi : gridInv ab = (ab.2 + 1, ab.1) := if_pos h
      have hcomm : (L.eraseIdx ab.1).eraseIdx ab.2
                    = (L.eraseIdx (ab.2 + 1)).eraseIdx ab.1 := eraseIdx_eraseIdx_comm L ab.1 ab.2 h
      show cochainAtNat σ (subsetIdx n k ((L.eraseIdx (gridInv ab).1).eraseIdx (gridInv ab).2))
            = cochainAtNat σ (subsetIdx n k ((L.eraseIdx ab.1).eraseIdx ab.2))
      have h1 : (gridInv ab).1 = ab.2 + 1 := congrArg Prod.fst hgi
      have h2 : (gridInv ab).2 = ab.1 := congrArg Prod.snd hgi
      exact congrArg (fun z => cochainAtNat σ (subsetIdx n k z))
        ((congrArg (fun u => (L.eraseIdx u).eraseIdx (gridInv ab).2) h1).trans
          ((congrArg (fun v => (L.eraseIdx (ab.2 + 1)).eraseIdx v) h2).trans hcomm.symm))
    · have h' : ab.2 < ab.1 := Nat.lt_of_not_le h
      have hgi : gridInv ab = (ab.2, ab.1 - 1) := if_neg h
      have hle : ab.2 ≤ ab.1 - 1 := Nat.le_sub_one_of_lt h'
      have hsucc : (ab.1 - 1) + 1 = ab.1 := Nat.succ_pred_eq_of_pos (Nat.lt_of_le_of_lt (Nat.zero_le _) h')
      have hcomm : (L.eraseIdx ab.2).eraseIdx (ab.1 - 1)
                    = (L.eraseIdx ((ab.1 - 1) + 1)).eraseIdx ab.2 :=
        eraseIdx_eraseIdx_comm L ab.2 (ab.1 - 1) hle
      have hcomm' : (L.eraseIdx ab.2).eraseIdx (ab.1 - 1)
                    = (L.eraseIdx ab.1).eraseIdx ab.2 :=
        hcomm.trans (congrArg (fun u => (L.eraseIdx u).eraseIdx ab.2) hsucc)
      show cochainAtNat σ (subsetIdx n k ((L.eraseIdx (gridInv ab).1).eraseIdx (gridInv ab).2))
            = cochainAtNat σ (subsetIdx n k ((L.eraseIdx ab.1).eraseIdx ab.2))
      have h1 : (gridInv ab).1 = ab.2 := congrArg Prod.fst hgi
      have h2 : (gridInv ab).2 = ab.1 - 1 := congrArg Prod.snd hgi
      exact congrArg (fun z => cochainAtNat σ (subsetIdx n k z))
        ((congrArg (fun u => (L.eraseIdx u).eraseIdx (gridInv ab).2) h1).trans
          ((congrArg (fun v => (L.eraseIdx ab.2).eraseIdx v) h2).trans hcomm'))

/-! ## The final assembly: `δ² = 0`, dimension-free -/

/-- `xorFold` is congruent in a pointwise-equal summand. -/
private theorem xorFold_congr {α : Type _} (f g : α → Bool) :
    ∀ (l : List α), (∀ a ∈ l, f a = g a) → xorFold f l = xorFold g l
  | [],      _ => rfl
  | x :: xs, h => by
    show xor (f x) (xorFold f xs) = xor (g x) (xorFold g xs)
    exact (congrArg (fun z => xor z (xorFold f xs)) (h x (List.Mem.head xs))).trans
      (congrArg (xor (g x)) (xorFold_congr f g xs (fun a ha => h a (List.Mem.tail x ha))))

/-- `cochainAtNat (delta σ) idx = deltaAt n k σ idx` in range (`delta σ` evaluated at a
    valid index is the inner `deltaAt`). -/
private theorem cochainAtNat_delta {n k : Nat} (σ : Cochain n k) {idx : Nat}
    (h : idx < binom n (k + 1)) : cochainAtNat (delta σ) idx = deltaAt n k σ idx :=
  (dif_pos h).trans (rfl : (delta σ) ⟨idx, h⟩ = deltaAt n k σ idx)

/-- The inner unfolding: at a valid outer face `(kSubset n (k+2) τ).eraseIdx a`, the outer
    summand is the inner `xorFold` over the double-erase face — the reverse round-trip
    (`kSubset_subsetIdx`) collapses `kSubset ∘ subsetIdx` to the genuine face. -/
private theorem delta_delta_inner {n k : Nat} (σ : Cochain n k)
    (τ : Fin (binom n (k + 2))) (a : Nat) (ha : a < k + 2) :
    cochainAtNat (delta σ) (subsetIdx n (k + 1) ((kSubset n (k + 2) τ.val).eraseIdx a))
      = xorFold (fun b => cochainAtNat σ
          (subsetIdx n k (((kSubset n (k + 2) τ.val).eraseIdx a).eraseIdx b))) (List.range (k + 1)) := by
  have hLsort : E213.Lib.Math.Cohomology.Examples.ColexRoundTrip.Sorted (kSubset n (k + 2) τ.val) :=
    kSubset_sorted n (k + 2) τ.val
  have hLlen : (kSubset n (k + 2) τ.val).length = k + 2 := kSubset_length n (k + 2) τ.val τ.isLt
  have hLbound : ∀ x ∈ kSubset n (k + 2) τ.val, x < n := kSubset_mem_lt n (k + 2) τ.val
  have ha' : a < (kSubset n (k + 2) τ.val).length := hLlen.symm ▸ ha
  have hfsort := sorted_eraseIdx (kSubset n (k + 2) τ.val) a hLsort
  have hflen : ((kSubset n (k + 2) τ.val).eraseIdx a).length = k + 1 :=
    Nat.succ.inj ((length_eraseIdx_of_lt _ a ha').trans hLlen)
  have hfbound : ∀ x ∈ (kSubset n (k + 2) τ.val).eraseIdx a, x < n :=
    fun x hx => hLbound x (mem_eraseIdx_imp_mem _ a x hx)
  have hguard : subsetIdx n (k + 1) ((kSubset n (k + 2) τ.val).eraseIdx a) < binom n (k + 1) :=
    subsetIdx_lt _ hfsort hfbound hflen
  have hrt : kSubset n (k + 1) (subsetIdx n (k + 1) ((kSubset n (k + 2) τ.val).eraseIdx a))
              = (kSubset n (k + 2) τ.val).eraseIdx a :=
    kSubset_subsetIdx n (k + 1) _ hfsort hfbound hflen
  calc cochainAtNat (delta σ) (subsetIdx n (k + 1) ((kSubset n (k + 2) τ.val).eraseIdx a))
      = deltaAt n k σ (subsetIdx n (k + 1) ((kSubset n (k + 2) τ.val).eraseIdx a)) :=
        cochainAtNat_delta σ hguard
    _ = xorFold (fun b => cochainAtNat σ (subsetIdx n k
            ((kSubset n (k + 1) (subsetIdx n (k + 1) ((kSubset n (k + 2) τ.val).eraseIdx a))).eraseIdx b)))
          (List.range (k + 1)) :=
        deltaAt_eq_xorFold σ _
    _ = _ :=
        congrArg (fun L' => xorFold (fun b => cochainAtNat σ (subsetIdx n k (L'.eraseIdx b)))
          (List.range (k + 1))) hrt

/-- ★★★★ **The dimension-free `δ² = 0`.**  For the 213-native ℤ/2 simplicial cochain
    complex, `δ (δ σ) = 0` for **every** cochain `σ` at **every** dimension `n` and degree
    `k` — the genuine chain-complex law, uniform in `n`, proven without `decide`/Fintype:
    `δ²σ(τ)` unfolds (twice `deltaAt_eq_xorFold`, the colex bijection collapsing the faces)
    to a XOR over the `(k+2)×(k+1)` removal grid, which the order-swap involution
    (`eraseIdx_eraseIdx_comm`) cancels to `0` (`grid_xorFold_zero`).  ∅-axiom. -/
theorem delta_sq_zero_general {n k : Nat} (σ : Cochain n k) (τ : Fin (binom n (k + 2))) :
    delta (delta σ) τ = false := by
  have h1 : delta (delta σ) τ
      = xorFold (fun a => cochainAtNat (delta σ)
          (subsetIdx n (k + 1) ((kSubset n (k + 2) τ.val).eraseIdx a))) (List.range (k + 2)) :=
    deltaAt_eq_xorFold (delta σ) τ.val
  have h2 := xorFold_congr _ _ (List.range (k + 2))
    (fun a ha => delta_delta_inner σ τ a (mem_range_lt a (k + 2) ha))
  have h3 := (xorFold_gridList
    (fun ab : Nat × Nat => cochainAtNat σ
      (subsetIdx n k (((kSubset n (k + 2) τ.val).eraseIdx ab.1).eraseIdx ab.2))) (k + 2) (k + 1)).symm
  exact (h1.trans (h2.trans h3)).trans (grid_xorFold_zero σ (kSubset n (k + 2) τ.val))

end E213.Lib.Math.Cohomology.DeltaSqZero
