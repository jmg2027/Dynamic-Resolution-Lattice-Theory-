import E213.Lib.Math.Algebra.Linalg213.Laplace
import E213.Lib.Math.Algebra.Linalg213.ProdCongr
import E213.Meta.Tactic.List213

/-!
# GaussLemma — Gauss's lemma (in progress)

Layer 2: the half-system `[1..m]` and the fold permutation.

`cntNodup_of_listNodup` bridges `List.Nodup` (Pairwise) to the count-based `Nodup` used by
`lperm_of_nodup_mem_iff`; `mem_of_card_le` is the pigeonhole (a `Nodup` sublist of equal-or-greater
length is a superset); `seg m = [1..m]` with its length / membership / `Nodup`.
-/

namespace E213.Lib.Math.NumberTheory.ModArith.GaussLemma

open E213.Lib.Math.Algebra.Linalg213.Permutation (iota LPerm map_lperm)
open E213.Lib.Math.Algebra.Linalg213.PermClosure
  (cnt Nodup cnt_eq_zero_of_not_mem cnt_pos_mem cnt_pos_of_mem lt_of_mem_iota length_iota)
open E213.Lib.Math.Algebra.Linalg213.Laplace (lperm_of_nodup_mem_iff mem_iota_of_lt)
open E213.Tactic.List213
  (nodup_map_of_inj nodup_append nodup_length_le_of_subset mem_filter_of
   length_filter_lt_of_mem length_map exists_of_mem_map mem_map_of_mem)
open E213.Tactic.NatHelper (add_right_cancel_pure)

/-! ## §1 — bridges and the pigeonhole -/

/-- `List.Nodup` (Pairwise) ⟹ the count-based `Nodup` (`∀ a, cnt a L ≤ 1`). -/
theorem cntNodup_of_listNodup {α : Type} [DecidableEq α] : ∀ {L : List α}, L.Nodup → Nodup L
  | [], _ => fun q => Nat.zero_le _
  | a :: l, h => fun q => by
    cases h with
    | cons hal hl =>
      show (if a = q then 1 else 0) + cnt q l ≤ 1
      by_cases haq : a = q
      · have hanl : a ∉ l := fun ham => (hal a ham) rfl
        have hql : cnt q l = 0 := cnt_eq_zero_of_not_mem (haq ▸ hanl)
        rw [if_pos haq, hql]; exact Nat.le_refl 1
      · rw [if_neg haq, Nat.zero_add]; exact cntNodup_of_listNodup hl q

/-- **Pigeonhole.**  A `Nodup` list `L1 ⊆ L2` with `|L2| ≤ |L1|` is a superset: every `v ∈ L2`
    lies in `L1` (else `L1 ⊆ L2 ∖ {v}` is strictly shorter than `L2 ≤ L1`). -/
theorem mem_of_card_le {α : Type} [DecidableEq α] {L1 L2 : List α} (h1 : L1.Nodup)
    (hsub : ∀ x, x ∈ L1 → x ∈ L2) (hlen : L2.length ≤ L1.length) :
    ∀ v, v ∈ L2 → v ∈ L1 := by
  intro v hv
  cases Nat.eq_zero_or_pos (cnt v L1) with
  | inr hpos => exact cnt_pos_mem hpos
  | inl hzero =>
    exfalso
    have hvL1 : v ∉ L1 := fun hm => Nat.lt_irrefl 0 (hzero ▸ cnt_pos_of_mem hm)
    have hsub' : ∀ x, x ∈ L1 → x ∈ L2.filter (fun a => if a = v then false else true) := by
      intro x hx
      have hxv : x ≠ v := fun e => hvL1 (e ▸ hx)
      exact mem_filter_of (hsub x hx) (if_neg hxv)
    have hle : L1.length ≤ (L2.filter (fun a => if a = v then false else true)).length :=
      nodup_length_le_of_subset h1 hsub'
    have hlt : (L2.filter (fun a => if a = v then false else true)).length < L2.length :=
      length_filter_lt_of_mem hv (if_pos rfl)
    exact Nat.lt_irrefl L1.length (Nat.lt_of_le_of_lt hle (Nat.lt_of_lt_of_le hlt hlen))

/-! ## §2 — the half-system `seg m = [1, 2, …, m]` -/

/-- `[1, 2, …, m]`. -/
def seg (m : Nat) : List Nat := (iota m).map (· + 1)

theorem seg_length (m : Nat) : (seg m).length = m := by rw [seg, length_map, length_iota]

theorem mem_seg {m v : Nat} : v ∈ seg m ↔ 1 ≤ v ∧ v ≤ m := by
  constructor
  · intro h
    obtain ⟨x, hx, hxv⟩ := exists_of_mem_map h
    have hxm : x < m := lt_of_mem_iota hx
    rw [← hxv]
    exact ⟨Nat.succ_le_succ (Nat.zero_le x), Nat.succ_le_of_lt hxm⟩
  · intro ⟨hv1, hvm⟩
    obtain ⟨w, hw⟩ : ∃ w, v = w + 1 := ⟨v - 1, (Nat.succ_pred_eq_of_pos hv1).symm⟩
    have hwm : w < m := by rw [hw] at hvm; exact Nat.lt_of_succ_le hvm
    rw [seg, hw]
    exact mem_map_of_mem (· + 1) (mem_iota_of_lt hwm)

/-- `iota n` is `List.Nodup` (each new tail-element `n` is fresh). -/
theorem listNodup_iota : ∀ n, (iota n).Nodup
  | 0 => List.Pairwise.nil
  | n + 1 => by
    show (iota n ++ [n]).Nodup
    refine nodup_append (listNodup_iota n)
      (List.Pairwise.cons (fun b hb => absurd hb (List.not_mem_nil b)) List.Pairwise.nil) ?_
    intro a ha hm
    have han : a = n := by
      cases hm with
      | head => rfl
      | tail _ h => exact absurd h (List.not_mem_nil a)
    have hlt : a < n := lt_of_mem_iota ha
    rw [han] at hlt
    exact Nat.lt_irrefl n hlt

theorem seg_listNodup (m : Nat) : (seg m).Nodup :=
  nodup_map_of_inj (fun _ _ _ _ h => add_right_cancel_pure h) (listNodup_iota m)

end E213.Lib.Math.NumberTheory.ModArith.GaussLemma
