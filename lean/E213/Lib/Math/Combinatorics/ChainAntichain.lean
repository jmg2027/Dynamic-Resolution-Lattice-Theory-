import E213.Lib.Math.Combinatorics.Sperner
import E213.Lib.Math.Combinatorics.SpernerChains

/-!
# Chain / antichain duality on the Boolean lattice (Mirsky's side, ∅-axiom)

Sperner (`SpernerChains.sperner_theorem`) bounded **antichains** by the largest
layer.  The dual viewpoint bounds **chains** and exposes Mirsky's theorem for the
Boolean lattice: the longest chain has `n + 1` elements, matching the `n + 1`
layers — the canonical antichain partition.

This file proves the **height bound** — every duplicate-free chain of `2^[n]` has
at most `n + 1` members — by the dual of Sperner's `SEPARATE`: in a *chain*
(every two members comparable) distinct members have **distinct sizes**
(`chain_card_inj`, from `eq_of_subseteq_card_eq`), so the size map embeds the
chain, nodup, into the `n + 1` possible sizes `{0, …, n}` (`idxList (n+1)`).
The `n + 1` layers (each an antichain, `Sperner.kLayer_isAntichain`) realise the
matching cover; a chain meets each layer at most once, so no antichain partition
can have fewer than the longest chain — the Mirsky equality for `2^[n]`.
-/

namespace E213.Lib.Math.Combinatorics.ChainAntichain

open E213.Lib.Math.Combinatorics.Sperner
  (cardB subseteqB comparable eq_of_subseteq_card_eq IsAntichain
   kLayer kLayer_isAntichain)
open E213.Lib.Math.Combinatorics.SpernerChains
  (idxList idxList_length mem_idxList_lt cardB_le_length)
open E213.Tactic.List213
  (mem_append_left mem_append_right exists_of_mem_map nodup_map_of_inj
   nodup_length_le_of_subset length_map)

/-- Every `k < m` is a position of `idxList m = [0, …, m−1]` (converse of
    `SpernerChains.mem_idxList_lt`). -/
theorem mem_idxList_of_lt : ∀ {m k : Nat}, k < m → k ∈ idxList m
  | 0, k, h => absurd h (Nat.not_lt_zero k)
  | m + 1, k, h => by
      show k ∈ idxList m ++ [m]
      rcases Nat.lt_or_ge k m with hkm | hkm
      · exact mem_append_left (mem_idxList_of_lt hkm)
      · have hkeq : k = m := Nat.le_antisymm (Nat.le_of_lt_succ h) hkm
        rw [hkeq]; exact mem_append_right _ (List.Mem.head _)

/-- ★ **The chain SEPARATE.**  In a chain, equal-size members coincide: if `A, B`
    are comparable and `|A| = |B|` then `A = B`.  (The dual of the antichain
    SEPARATE — there, comparability is forbidden; here, it forces a size gap.) -/
theorem chain_card_inj {A B : List Bool} (hc : comparable A B = true)
    (heq : cardB A = cardB B) : A = B := by
  cases hab : subseteqB A B with
  | true => exact eq_of_subseteq_card_eq A B hab heq
  | false =>
      cases hba : subseteqB B A with
      | true => exact (eq_of_subseteq_card_eq B A hba heq.symm).symm
      | false =>
          exfalso
          have hcf : comparable A B = false := by
            show (subseteqB A B || subseteqB B A) = false
            rw [hab, hba]; rfl
          rw [hcf] at hc; exact Bool.noConfusion hc

/-- A chain: every two members are comparable (reflexively, so self-comparison is
    free).  `2^[n]` chains are the totally-ordered sub-families. -/
def IsChain (L : List (List Bool)) : Prop :=
  ∀ A, A ∈ L → ∀ B, B ∈ L → comparable A B = true

/-- ★ **The Boolean lattice's height.**  Every duplicate-free chain of `2^[n]`
    (length-`n` `Bool` vectors, pairwise comparable) has at most `n + 1` members
    — the dual of Sperner.  Its sizes are distinct (`chain_card_inj`) and lie in
    `{0, …, n}`, so the size map injects the chain into `idxList (n+1)`. -/
theorem chain_length_le {n : Nat} (L : List (List Bool))
    (hch : IsChain L) (hnd : L.Nodup) (hlen : ∀ A, A ∈ L → A.length = n) :
    L.length ≤ n + 1 := by
  have hsizes_nd : (L.map cardB).Nodup :=
    nodup_map_of_inj (fun A hA B hB heq => chain_card_inj (hch A hA B hB) heq) hnd
  have hsub : ∀ k, k ∈ L.map cardB → k ∈ idxList (n + 1) := by
    intro k hk
    obtain ⟨A, hA, rfl⟩ := exists_of_mem_map hk
    exact mem_idxList_of_lt
      (Nat.lt_succ_of_le (Nat.le_trans (cardB_le_length A) (Nat.le_of_eq (hlen A hA))))
  have hle := nodup_length_le_of_subset hsizes_nd hsub
  rw [length_map, idxList_length] at hle
  exact hle

/-- ★ **A chain meets a layer at most once** (the dual cap).  Two members of a
    chain that share a size are equal, so any chain has ≤ 1 element in each
    size-layer — the per-antichain cap that makes the `n + 1` layers the minimum
    antichain partition.  (`Sperner.kLayer_isAntichain` gives that the layers
    *are* antichains; together this is Mirsky for `2^[n]`: longest chain = `n+1`
    = number of layers.) -/
theorem chain_layer_cap {L : List (List Bool)} (hch : IsChain L)
    {A B : List Bool} (hA : A ∈ L) (hB : B ∈ L)
    (hcA : cardB A = cardB B) : A = B :=
  chain_card_inj (hch A hA B hB) hcA

end E213.Lib.Math.Combinatorics.ChainAntichain
