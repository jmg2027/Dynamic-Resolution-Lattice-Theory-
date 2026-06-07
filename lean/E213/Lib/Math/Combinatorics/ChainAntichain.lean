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
  (cardB subseteqB comparable impl eq_of_subseteq_card_eq IsAntichain beq_self cardEq
   kLayer kLayer_isAntichain half half_le le_half kLayer_card kLayer_nodup cardEq)
open E213.Lib.Math.Combinatorics.SpernerChains
  (idxList idxList_length idxList_nodup mem_idxList_lt cardB_le_length
   beqBoolList beqBoolList_refl eq_of_beqBoolList)
open E213.Lib.Math.Combinatorics.BoolEnum (mem_allBoolLists length_of_mem_allBoolLists)
open E213.Lib.Physics.Simplex.Counts (binom)
open E213.Tactic.List213
  (mem_append_left mem_append_right exists_of_mem_map mem_map_of_mem nodup_map_of_inj
   nodup_length_le_of_subset length_map mem_filter_of mem_filter nodup_append mem_append_iff)

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

/-! ## §2 — the maximum chain: the height is exactly `n + 1`

The canonical chain `∅ ⊂ {0} ⊂ … ⊂ [n]`: `initSeg k n` = the first `k` positions
`true`.  It is a chain (nested prefixes), duplicate-free (distinct sizes), and has
`n + 1` members — matching `chain_length_le`, so the Boolean lattice's height is
**exactly** `n + 1`. -/

/-- `initSeg k n` = `k` `true`s then `(n − k)` `false`s (length `n`). -/
def initSeg : Nat → Nat → List Bool
  | 0, 0 => []
  | 0, n + 1 => false :: initSeg 0 n
  | k + 1, 0 => []
  | k + 1, n + 1 => true :: initSeg k n

theorem initSeg_length : ∀ (k n : Nat), (initSeg k n).length = n
  | 0, 0 => rfl
  | 0, n + 1 => by show (initSeg 0 n).length + 1 = n + 1; rw [initSeg_length 0 n]
  | k + 1, 0 => rfl
  | k + 1, n + 1 => by show (initSeg k n).length + 1 = n + 1; rw [initSeg_length k n]

theorem initSeg_zero_card : ∀ n, cardB (initSeg 0 n) = 0
  | 0 => rfl
  | n + 1 => by show cardB (initSeg 0 n) = 0; exact initSeg_zero_card n

theorem initSeg_card : ∀ (k n : Nat), k ≤ n → cardB (initSeg k n) = k
  | 0, n, _ => initSeg_zero_card n
  | k + 1, 0, h => absurd h (Nat.not_succ_le_zero k)
  | k + 1, n + 1, h => by
      show cardB (initSeg k n) + 1 = k + 1
      rw [initSeg_card k n (Nat.le_of_succ_le_succ h)]

/-- The prefixes nest: `j ≤ k ≤ n → initSeg j n ⊆ initSeg k n`. -/
theorem initSeg_mono : ∀ (n j k : Nat), j ≤ k → k ≤ n →
    subseteqB (initSeg j n) (initSeg k n) = true
  | 0, j, k, hjk, hkn => by
      have hk0 : k = 0 := Nat.le_antisymm hkn (Nat.zero_le k)
      have hj0 : j = 0 := Nat.le_antisymm (hk0 ▸ hjk) (Nat.zero_le j)
      rw [hj0, hk0]; rfl
  | n + 1, j, k, hjk, hkn => by
      cases j with
      | zero => cases k with
        | zero =>
            show (impl false false && subseteqB (initSeg 0 n) (initSeg 0 n)) = true
            rw [show impl false false = true from rfl, Bool.true_and]
            exact initSeg_mono n 0 0 (Nat.le_refl 0) (Nat.zero_le n)
        | succ k' =>
            show (impl false true && subseteqB (initSeg 0 n) (initSeg k' n)) = true
            rw [show impl false true = true from rfl, Bool.true_and]
            exact initSeg_mono n 0 k' (Nat.zero_le k') (Nat.le_of_succ_le_succ hkn)
      | succ j' => cases k with
        | zero => exact absurd hjk (Nat.not_succ_le_zero j')
        | succ k' =>
            show (impl true true && subseteqB (initSeg j' n) (initSeg k' n)) = true
            rw [show impl true true = true from rfl, Bool.true_and]
            exact initSeg_mono n j' k' (Nat.le_of_succ_le_succ hjk) (Nat.le_of_succ_le_succ hkn)

/-- Comparability of two prefixes (either nests in the other). -/
theorem initSeg_comparable (n j k : Nat) (hj : j ≤ n) (hk : k ≤ n) :
    comparable (initSeg j n) (initSeg k n) = true := by
  rcases Nat.le_total j k with hjk | hkj
  · show (subseteqB (initSeg j n) (initSeg k n) || subseteqB (initSeg k n) (initSeg j n)) = true
    rw [initSeg_mono n j k hjk hk]; rfl
  · show (subseteqB (initSeg j n) (initSeg k n) || subseteqB (initSeg k n) (initSeg j n)) = true
    rw [initSeg_mono n k j hkj hj]; cases subseteqB (initSeg j n) (initSeg k n) <;> rfl

/-- The canonical maximum chain `[initSeg 0 n, …, initSeg n n]`. -/
def canonChain (n : Nat) : List (List Bool) := (idxList (n + 1)).map (fun k => initSeg k n)

/-- ★ **The height is achieved.**  The canonical chain is a duplicate-free chain
    of `2^[n]` with exactly `n + 1` members — so (with `chain_length_le`) the
    Boolean lattice's height is **exactly** `n + 1`. -/
theorem canonChain_max (n : Nat) :
    IsChain (canonChain n) ∧ (canonChain n).Nodup
      ∧ (∀ A, A ∈ canonChain n → A.length = n) ∧ (canonChain n).length = n + 1 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro A hA B hB
    obtain ⟨j, hj, rfl⟩ := exists_of_mem_map hA
    obtain ⟨k, hk, rfl⟩ := exists_of_mem_map hB
    exact initSeg_comparable n j k
      (Nat.le_of_lt_succ (mem_idxList_lt hj)) (Nat.le_of_lt_succ (mem_idxList_lt hk))
  · refine nodup_map_of_inj (fun j hj k hk heq => ?_) (idxList_nodup (n + 1))
    have hjn : j ≤ n := Nat.le_of_lt_succ (mem_idxList_lt hj)
    have hkn : k ≤ n := Nat.le_of_lt_succ (mem_idxList_lt hk)
    have hc := congrArg cardB heq
    rw [initSeg_card j n hjn, initSeg_card k n hkn] at hc
    exact hc
  · intro A hA
    obtain ⟨k, _, rfl⟩ := exists_of_mem_map hA
    exact initSeg_length k n
  · show ((idxList (n + 1)).map (fun k => initSeg k n)).length = n + 1
    rw [length_map, idxList_length]

/-! ## §3 — Mirsky for `2^[n]`

The longest chain has `n + 1` elements (`canonChain_max` + `chain_length_le`), and
the `n + 1` layers are the matching antichain partition: every length-`n` vector
lies in its size-layer `kLayer n (cardB A)` (`Sperner.kLayer_isAntichain`), and a
chain meets each layer ≤ once (`chain_layer_cap`).  So the minimum antichain
partition equals the longest chain — Mirsky's theorem on the Boolean lattice. -/

/-- Every length-`n` vector lies in its size-layer (the layers cover `2^[n]`). -/
theorem mem_own_layer {A : List Bool} {n : Nat} (hn : A.length = n) :
    A ∈ kLayer n (cardB A) := by
  refine mem_filter_of ?_ ?_
  · have := mem_allBoolLists A; rwa [hn] at this
  · show Nat.beq (cardB A) (cardB A) = true; exact beq_self _

/-- ★★ **Mirsky's theorem on the Boolean lattice.**  (1) the longest chain has
    exactly `n + 1` members; (2) every chain is bounded by `n + 1`; (3) the
    `n + 1` size-layers are antichains covering `2^[n]` — the matching minimum
    antichain partition.  Longest chain = `n + 1` = #layers. -/
theorem mirsky_boolean (n : Nat) :
    (∃ L, IsChain L ∧ L.Nodup ∧ (∀ A, A ∈ L → A.length = n) ∧ L.length = n + 1)
    ∧ (∀ L, IsChain L → L.Nodup → (∀ A, A ∈ L → A.length = n) → L.length ≤ n + 1)
    ∧ (∀ A, A.length = n → A ∈ kLayer n (cardB A) ∧ IsAntichain (kLayer n (cardB A))) :=
  ⟨⟨canonChain n, canonChain_max n⟩,
   fun L hch hnd hlen => chain_length_le L hch hnd hlen,
   fun A hn => ⟨mem_own_layer hn, kLayer_isAntichain n (cardB A)⟩⟩

/-! ## §4 — Dilworth's bound on `2^[n]` (the chain-cover dual)

Dilworth: the minimum number of **chains** to cover a poset equals the maximum
antichain.  For `2^[n]` both are `C(n, ⌊n/2⌋)` (Sperner).  The **lower bound** —
any chain cover needs `≥ C(n,⌊n/2⌋)` chains — is the clean dual of Mirsky's
lower bound: the middle layer is an antichain of that size, a chain holds ≤ 1 of
its members (`chain_card_inj`), so distinct middle members need distinct chains.
The matching **upper bound** (a `C(n,⌊n/2⌋)`-chain cover exists) is the de
Bruijn–Tengbergen–Kruyswijk *symmetric chain decomposition* — recorded as the
open rung.  -/

/-- `Bool` membership of a vector in a chain (decidable, propext-free). -/
def memBL (A : List Bool) : List (List Bool) → Bool
  | [] => false
  | v :: rest => beqBoolList A v || memBL A rest

theorem memBL_of_mem {A : List Bool} : ∀ {C : List (List Bool)}, A ∈ C → memBL A C = true
  | v :: rest, h => by
      cases h with
      | head =>
          show (beqBoolList A A || memBL A rest) = true
          rw [beqBoolList_refl A, Bool.true_or]
      | tail _ h' =>
          show (beqBoolList A v || memBL A rest) = true
          rw [memBL_of_mem h']; cases beqBoolList A v <;> rfl

theorem mem_of_memBL {A : List Bool} : ∀ {C : List (List Bool)}, memBL A C = true → A ∈ C
  | v :: rest, h => by
      cases hb : beqBoolList A v with
      | true => rw [eq_of_beqBoolList A v hb]; exact List.Mem.head _
      | false =>
          have h' : memBL A rest = true := by
            have : (beqBoolList A v || memBL A rest) = true := h
            rw [hb, Bool.false_or] at this; exact this
          exact List.Mem.tail _ (mem_of_memBL h')

/-- The first chain of the cover that contains `A` (`[]` if none). -/
def findChain (A : List Bool) : List (List (List Bool)) → List (List Bool)
  | [] => []
  | C :: rest => bif memBL A C then C else findChain A rest

theorem findChain_spec (A : List Bool) : ∀ (chains : List (List (List Bool))),
    (∃ C, C ∈ chains ∧ A ∈ C) → findChain A chains ∈ chains ∧ A ∈ findChain A chains
  | [], ⟨C, hC, _⟩ => absurd hC (List.not_mem_nil C)
  | D :: rest, ⟨C, hC, hAC⟩ => by
      show (bif memBL A D then D else findChain A rest) ∈ D :: rest
          ∧ A ∈ (bif memBL A D then D else findChain A rest)
      cases hm : memBL A D with
      | true => exact ⟨List.Mem.head _, mem_of_memBL hm⟩
      | false =>
          have hCrest : C ∈ rest := by
            cases hC with
            | head => rw [memBL_of_mem hAC] at hm; exact Bool.noConfusion hm
            | tail _ h => exact h
          obtain ⟨h1, h2⟩ := findChain_spec A rest ⟨C, hCrest, hAC⟩
          exact ⟨List.Mem.tail _ h1, h2⟩

/-- ★★ **Dilworth's lower bound on `2^[n]`.**  Any cover of the middle layer by
    chains needs at least `C(n, ⌊n/2⌋)` chains — so the minimum chain cover of
    `2^[n]` is `≥ C(n, ⌊n/2⌋)` = the maximum antichain (Sperner).  The dual of
    Mirsky's lower bound. -/
theorem dilworth_lower {n : Nat} (chains : List (List (List Bool)))
    (hch : ∀ C, C ∈ chains → IsChain C)
    (hcov : ∀ A, A ∈ kLayer n (half n) → ∃ C, C ∈ chains ∧ A ∈ C) :
    binom n (half n) ≤ chains.length := by
  have hcard : ∀ A, A ∈ kLayer n (half n) → cardB A = half n :=
    fun A hA => Nat.eq_of_beq_eq_true (mem_filter hA).2
  have hinj : ∀ A, A ∈ kLayer n (half n) → ∀ B, B ∈ kLayer n (half n) →
      findChain A chains = findChain B chains → A = B := by
    intro A hA B hB heq
    obtain ⟨_, hACA⟩ := findChain_spec A chains (hcov A hA)
    obtain ⟨hCB, hBCB⟩ := findChain_spec B chains (hcov B hB)
    rw [heq] at hACA
    exact chain_card_inj ((hch _ hCB) A hACA B hBCB) ((hcard A hA).trans (hcard B hB).symm)
  have hmapnd : ((kLayer n (half n)).map (fun A => findChain A chains)).Nodup :=
    nodup_map_of_inj hinj (kLayer_nodup n (half n))
  have hsub : ∀ x, x ∈ (kLayer n (half n)).map (fun A => findChain A chains) → x ∈ chains := by
    intro x hx
    obtain ⟨A, hA, rfl⟩ := exists_of_mem_map hx
    exact (findChain_spec A chains (hcov A hA)).1
  have hle := nodup_length_le_of_subset hmapnd hsub
  rw [length_map, kLayer_card] at hle
  exact hle

/-! ## §5 — chain-property infrastructure for the SCD

Toward the Dilworth upper bound (the symmetric chain decomposition): a list whose
members are pairwise `subseteqB`-ordered is a chain (`sorted_isChain`).  The SCD's
recursive constructors prepend a bit and append a top element; the `subseteqB`
facts below (`subseteqB_refl`, `subseteqB_false_true`) feed the preservation of
the sorted property. -/

/-- Subset reflexivity: `A ⊆ A`. -/
theorem subseteqB_refl : ∀ (A : List Bool), subseteqB A A = true
  | [] => rfl
  | a :: as => by
      show (impl a a && subseteqB as as) = true
      rw [subseteqB_refl as]; cases a <;> rfl

/-- `comparable A A = true`. -/
theorem comparable_refl (A : List Bool) : comparable A A = true := by
  show (subseteqB A A || subseteqB A A) = true
  rw [subseteqB_refl A]; rfl

/-- Adding the new element only at the top: `false :: v ⊆ true :: v`. -/
theorem subseteqB_false_true (v : List Bool) : subseteqB (false :: v) (true :: v) = true := by
  show (impl false true && subseteqB v v) = true
  rw [subseteqB_refl v]; rfl

/-- Prepending the same bit preserves `⊆`: `subseteqB (b::v) (b::w) = subseteqB v w`. -/
theorem subseteqB_cons_same (b : Bool) (v w : List Bool) :
    subseteqB (b :: v) (b :: w) = subseteqB v w := by
  show (impl b b && subseteqB v w) = subseteqB v w
  cases b <;> rfl

/-- A `Pairwise`-related list relates any two members in *some* order (the list's
    order witnesses it — no transitivity needed). -/
theorem pairwise_rel {α : Type _} {R : α → α → Prop} :
    ∀ {L : List α}, List.Pairwise R L →
      ∀ A, A ∈ L → ∀ B, B ∈ L → A = B ∨ R A B ∨ R B A
  | x :: xs, hp, A, hA, B, hB => by
      cases hp with
      | cons hx hxs =>
          cases hA with
          | head => cases hB with
            | head => exact Or.inl rfl
            | tail _ hB' => exact Or.inr (Or.inl (hx B hB'))
          | tail _ hA' => cases hB with
            | head => exact Or.inr (Or.inr (hx A hA'))
            | tail _ hB' => exact pairwise_rel hxs A hA' B hB'

/-- ★ **Sorted ⟹ chain.**  A `subseteqB`-`Pairwise` list is a chain (any two
    members are comparable).  The bridge from the SCD's sorted constructors to
    `IsChain`. -/
theorem sorted_isChain {L : List (List Bool)}
    (h : List.Pairwise (fun A B => subseteqB A B = true) L) : IsChain L := by
  intro A hA B hB
  rcases pairwise_rel h A hA B hB with hab | hsub | hsub
  · rw [hab]; exact comparable_refl B
  · show (subseteqB A B || subseteqB B A) = true
    rw [hsub]; rfl
  · show (subseteqB A B || subseteqB B A) = true
    rw [hsub]; cases subseteqB A B <;> rfl

/-! ## §6 — the symmetric chain decomposition (construction + chain property)

The de Bruijn–Tengbergen–Kruyswijk recursion (new bit at the front): each chain
`C` of `2^[n]` yields `extendC C` (the chain with the new element absent, then
present at the top — one level higher) and `raiseC C` (the new element present,
top dropped — one level lower).  Both are chains; here we build the construction
and prove the chain property (`scd_isChain`).  The partition + the
symmetric-level count `= C(n,⌊n/2⌋)` remain (frontier). -/

/-- Extend a chain upward with the new element. -/
def extendC : List (List Bool) → List (List Bool)
  | [] => []
  | [v] => [false :: v, true :: v]
  | v :: rest => (false :: v) :: extendC rest

/-- Raise a chain (new element present, top dropped). -/
def raiseC : List (List Bool) → List (List Bool)
  | [] => []
  | [_] => []
  | v :: rest => (true :: v) :: raiseC rest

/-- `Sorted` = `subseteqB`-`Pairwise`. -/
abbrev Sorted (L : List (List Bool)) : Prop :=
  List.Pairwise (fun A B => subseteqB A B = true) L

/-- `v ⊆` everything below ⟹ `false :: v ⊆` everything in `extendC`. -/
theorem extendC_head (v : List Bool) : ∀ (rest : List (List Bool)),
    (∀ w, w ∈ rest → subseteqB v w = true) →
    ∀ x, x ∈ extendC rest → subseteqB (false :: v) x = true
  | [], _, _, hx => nomatch hx
  | [w], h, x, hx => by
      have hvw : subseteqB v w = true := h w (List.Mem.head _)
      cases hx with
      | head => show subseteqB (false :: v) (false :: w) = true; rw [subseteqB_cons_same]; exact hvw
      | tail _ hx' => cases hx' with
        | head =>
            show (impl false true && subseteqB v w) = true
            rw [show impl false true = true from rfl, Bool.true_and]; exact hvw
        | tail _ h'' => nomatch h''
  | w :: w2 :: rest', h, x, hx => by
      cases hx with
      | head =>
          show subseteqB (false :: v) (false :: w) = true
          rw [subseteqB_cons_same]; exact h w (List.Mem.head _)
      | tail _ hx' =>
          exact extendC_head v (w2 :: rest') (fun w' hw' => h w' (List.Mem.tail _ hw')) x hx'

/-- `v ⊆` everything below ⟹ `true :: v ⊆` everything in `raiseC`. -/
theorem raiseC_head (v : List Bool) : ∀ (rest : List (List Bool)),
    (∀ w, w ∈ rest → subseteqB v w = true) →
    ∀ x, x ∈ raiseC rest → subseteqB (true :: v) x = true
  | [], _, _, hx => nomatch hx
  | [_], _, _, hx => nomatch hx
  | w :: w2 :: rest', h, x, hx => by
      cases hx with
      | head =>
          show subseteqB (true :: v) (true :: w) = true
          rw [subseteqB_cons_same]; exact h w (List.Mem.head _)
      | tail _ hx' =>
          exact raiseC_head v (w2 :: rest') (fun w' hw' => h w' (List.Mem.tail _ hw')) x hx'

theorem extendC_sorted : ∀ (C : List (List Bool)), Sorted C → Sorted (extendC C)
  | [], _ => List.Pairwise.nil
  | [v], _ =>
      List.Pairwise.cons
        (fun x hx => by cases hx with
          | head => exact subseteqB_false_true v
          | tail _ h => nomatch h)
        (List.Pairwise.cons (fun _ h => nomatch h) List.Pairwise.nil)
  | v :: w :: rest, hs => by
      cases hs with
      | cons hhead htail =>
          exact List.Pairwise.cons
            (extendC_head v (w :: rest) hhead)
            (extendC_sorted (w :: rest) htail)

theorem raiseC_sorted : ∀ (C : List (List Bool)), Sorted C → Sorted (raiseC C)
  | [], _ => List.Pairwise.nil
  | [_], _ => List.Pairwise.nil
  | v :: w :: rest, hs => by
      cases hs with
      | cons hhead htail =>
          exact List.Pairwise.cons
            (raiseC_head v (w :: rest) hhead)
            (raiseC_sorted (w :: rest) htail)

/-- One step of the SCD recursion on a chain `C`. -/
def scdStep (C : List (List Bool)) : List (List (List Bool)) :=
  match raiseC C with
  | [] => [extendC C]
  | _ => [extendC C, raiseC C]

theorem mem_scdStep {C D : List (List Bool)} (h : C ∈ scdStep D) :
    C = extendC D ∨ C = raiseC D := by
  unfold scdStep at h
  cases hr : raiseC D with
  | nil =>
      rw [hr] at h
      cases h with
      | head => exact Or.inl rfl
      | tail _ h' => nomatch h'
  | cons a as =>
      rw [hr] at h
      cases h with
      | head => exact Or.inl rfl
      | tail _ h' => cases h' with
        | head => exact Or.inr rfl
        | tail _ h'' => nomatch h''

open E213.Lib.Math.Combinatorics.Permutations
  (flatMap213 mem_flatMap213 mem_flatMap213_of nodup_flatMap213)

/-- The symmetric chain decomposition of `2^[n]`. -/
def scd : Nat → List (List (List Bool))
  | 0 => [[[]]]
  | n + 1 => flatMap213 scdStep (scd n)

/-- Every chain produced by the SCD is `Sorted`. -/
theorem scd_sorted : ∀ (n : Nat) (C : List (List Bool)), C ∈ scd n → Sorted C
  | 0, C, h => by
      cases h with
      | head => exact List.Pairwise.cons (fun _ h => nomatch h) List.Pairwise.nil
      | tail _ h' => nomatch h'
  | n + 1, C, h => by
      obtain ⟨D, hD, hCD⟩ := mem_flatMap213 h
      rcases mem_scdStep hCD with rfl | rfl
      · exact extendC_sorted D (scd_sorted n D hD)
      · exact raiseC_sorted D (scd_sorted n D hD)

/-- ★★ **The SCD chains are chains.**  Every member of `scd n` is a chain of
    `2^[n]` (via `sorted_isChain`).  The chain-property half of the Dilworth
    upper bound; the partition + the count `= C(n,⌊n/2⌋)` remain (frontier). -/
theorem scd_isChain (n : Nat) (C : List (List Bool)) (h : C ∈ scd n) : IsChain C :=
  sorted_isChain (scd_sorted n C h)

/-! ## §7 — the SCD covers `2^[n]` (obligation b: the cover) -/

/-- `v ∈ C ⟹ false :: v ∈ extendC C` (the new element absent). -/
theorem false_mem_extendC (v : List Bool) : ∀ (C : List (List Bool)),
    v ∈ C → false :: v ∈ extendC C
  | [], h => nomatch h
  | [_], h => by
      cases h with
      | head => exact List.Mem.head _
      | tail _ h' => nomatch h'
  | _ :: w2 :: rest, h => by
      cases h with
      | head => exact List.Mem.head _
      | tail _ h' => exact List.Mem.tail _ (false_mem_extendC v (w2 :: rest) h')

/-- `v ∈ C ⟹ true :: v` is in `extendC C` (if `v` is the top) or `raiseC C`. -/
theorem true_mem (v : List Bool) : ∀ (C : List (List Bool)),
    v ∈ C → true :: v ∈ extendC C ∨ true :: v ∈ raiseC C
  | [], h => nomatch h
  | [_], h => by
      cases h with
      | head => exact Or.inl (List.Mem.tail _ (List.Mem.head _))
      | tail _ h' => nomatch h'
  | _ :: w2 :: rest, h => by
      cases h with
      | head => exact Or.inr (List.Mem.head _)
      | tail _ h' =>
          rcases true_mem v (w2 :: rest) h' with hh | hh
          · exact Or.inl (List.Mem.tail _ hh)
          · exact Or.inr (List.Mem.tail _ hh)

theorem extendC_mem_scdStep (C : List (List Bool)) : extendC C ∈ scdStep C := by
  unfold scdStep; cases raiseC C with
  | nil => exact List.Mem.head _
  | cons _ _ => exact List.Mem.head _

theorem raiseC_mem_scdStep {C : List (List Bool)} {x : List Bool}
    (hx : x ∈ raiseC C) : raiseC C ∈ scdStep C := by
  unfold scdStep; cases hr : raiseC C with
  | nil => rw [hr] at hx; nomatch hx
  | cons a as => exact List.Mem.tail _ (List.Mem.head _)

/-- ★★ **The SCD covers `2^[n]`.**  Every length-`n` vector lies in some chain of
    `scd n` — so (with `scd_isChain`) `scd n` is a chain cover of `2^[n]`. -/
theorem scd_cover : ∀ (n : Nat) (A : List Bool), A.length = n → ∃ C, C ∈ scd n ∧ A ∈ C
  | 0, A, hA => by
      cases A with
      | nil => exact ⟨[[]], List.Mem.head _, List.Mem.head _⟩
      | cons b v => nomatch hA
  | n + 1, A, hA => by
      cases A with
      | nil => nomatch hA
      | cons b v =>
          obtain ⟨C, hC, hvC⟩ := scd_cover n v (Nat.succ.inj hA)
          cases b with
          | false =>
              exact ⟨extendC C, mem_flatMap213_of hC (extendC_mem_scdStep C),
                     false_mem_extendC v C hvC⟩
          | true =>
              rcases true_mem v C hvC with h | h
              · exact ⟨extendC C, mem_flatMap213_of hC (extendC_mem_scdStep C), h⟩
              · exact ⟨raiseC C, mem_flatMap213_of hC (raiseC_mem_scdStep h), h⟩

/-- ★★ **`scd n` is a chain cover of `2^[n]`** — every member a chain, every
    vector covered.  The Dilworth upper bound needs only `|scd n| = C(n,⌊n/2⌋)`
    (the symmetric-level count) on top of this. -/
theorem scd_chain_cover (n : Nat) :
    (∀ C, C ∈ scd n → IsChain C) ∧ (∀ A, A.length = n → ∃ C, C ∈ scd n ∧ A ∈ C) :=
  ⟨scd_isChain n, scd_cover n⟩

/-! ## §8 — nonemptiness (infra for the count) -/

theorem extendC_ne_nil : ∀ (C : List (List Bool)), C ≠ [] → extendC C ≠ []
  | [], h => absurd rfl h
  | [_], _ => fun hc => List.noConfusion hc
  | _ :: _ :: _, _ => fun hc => List.noConfusion hc

theorem scdStep_ne_nil {C D : List (List Bool)} (hD : D ≠ []) (h : C ∈ scdStep D) : C ≠ [] := by
  unfold scdStep at h
  cases hr : raiseC D with
  | nil =>
      rw [hr] at h
      cases h with
      | head => exact extendC_ne_nil D hD
      | tail _ h' => nomatch h'
  | cons a as =>
      rw [hr] at h
      cases h with
      | head => exact extendC_ne_nil D hD
      | tail _ h' => cases h' with
        | head => exact fun hc => List.noConfusion hc
        | tail _ h'' => nomatch h''

/-- Every chain produced by the SCD is nonempty. -/
theorem scd_nonempty : ∀ (n : Nat) (C : List (List Bool)), C ∈ scd n → C ≠ []
  | 0, _, h => by
      cases h with
      | head => exact fun hc => List.noConfusion hc
      | tail _ h' => nomatch h'
  | n + 1, _, h => by
      obtain ⟨D, hD, hCD⟩ := mem_flatMap213 h
      exact scdStep_ne_nil (scd_nonempty n D hD) hCD

/-! ## §9 — the symmetric-level invariant (toward the count)

A chain's `cardB` values form a consecutive run `[k, k+1, …]` (`consec`); the
constructors shift it (`extendC` extends the run by one at the top; `raiseC`
drops the bottom and shifts up by one).  This tracks the level-span needed for
"each chain has exactly one `⌊n/2⌋`-element" — the count `|scd n| = C(n,⌊n/2⌋)`. -/

/-- The consecutive run `[k, k+1, …, k+m−1]`. -/
def consec : Nat → Nat → List Nat
  | _, 0 => []
  | k, m + 1 => k :: consec (k + 1) m

/-- `extendC` extends the `cardB` run by one at the top. -/
theorem extendC_sym : ∀ (C : List (List Bool)) (k : Nat),
    C ≠ [] → C.map cardB = consec k C.length →
    (extendC C).map cardB = consec k (C.length + 1)
  | [], _, h, _ => absurd rfl h
  | [v], k, _, hc => by
      have hk : cardB v = k := (List.cons.inj hc).1
      show [cardB v, cardB v + 1] = consec k 2
      rw [hk]; rfl
  | v :: w :: rest, k, _, hc => by
      have hk : cardB v = k := (List.cons.inj hc).1
      have htail : (w :: rest).map cardB = consec (k + 1) (w :: rest).length :=
        (List.cons.inj hc).2
      show cardB v :: (extendC (w :: rest)).map cardB
          = consec k ((w :: rest).length + 1 + 1)
      rw [extendC_sym (w :: rest) (k + 1) (fun hc => List.noConfusion hc) htail, hk]; rfl

/-- `raiseC` shifts the `cardB` run up by one and drops the bottom. -/
theorem raiseC_sym : ∀ (v w : List Bool) (rest : List (List Bool)) (k : Nat),
    (v :: w :: rest).map cardB = consec k (v :: w :: rest).length →
    (raiseC (v :: w :: rest)).map cardB = consec (k + 1) (w :: rest).length
  | v, w, [], k, hc => by
      have hk : cardB v = k := (List.cons.inj hc).1
      show [cardB v + 1] = consec (k + 1) 1
      rw [hk]; rfl
  | v, w, x :: rest', k, hc => by
      have hk : cardB v = k := (List.cons.inj hc).1
      have htail : (w :: x :: rest').map cardB = consec (k + 1) (w :: x :: rest').length :=
        (List.cons.inj hc).2
      show (cardB v + 1) :: (raiseC (w :: x :: rest')).map cardB
          = consec (k + 1) ((x :: rest').length + 1)
      rw [raiseC_sym w x rest' (k + 1) htail, hk]; rfl

/-! ## §10 — the symmetric-level invariant `SymChain` and its preservation

`SymChain n C` packages the run characterization with the symmetric span: the
`cardB` values are the contiguous run `[k, …, k + |C| − 1]` *and* `2k + |C| = n + 1`
(so the run is centred — it runs from level `k` to level `n − k`).  This is the
de Bruijn–Tengbergen–Kruyswijk invariant; `scd_sym` proves every chain in
`scd n` satisfies it.  It yields "each chain meets the middle layer `⌊n/2⌋`
exactly once", hence the count `|scd n| = C(n, ⌊n/2⌋)`. -/

/-- `(consec k m).length = m`. -/
theorem consec_length : ∀ (k m : Nat), (consec k m).length = m
  | _, 0 => rfl
  | k, m + 1 => by
      show (consec (k + 1) m).length + 1 = m + 1
      rw [consec_length (k + 1) m]

/-- `extendC` adds one chain element. -/
theorem extendC_length : ∀ (C : List (List Bool)), C ≠ [] →
    (extendC C).length = C.length + 1
  | [], h => absurd rfl h
  | [_], _ => rfl
  | v :: w :: rest, _ => by
      show (extendC (w :: rest)).length + 1 = (w :: rest).length + 1 + 1
      rw [extendC_length (w :: rest) (fun h => List.noConfusion h)]

/-- `raiseC` drops the top chain element. -/
theorem raiseC_length : ∀ (v w : List Bool) (rest : List (List Bool)),
    (raiseC (v :: w :: rest)).length = (w :: rest).length
  | _, _, [] => rfl
  | _, w, x :: rest' => by
      show (raiseC (w :: x :: rest')).length + 1 = (x :: rest').length + 1
      rw [raiseC_length w x rest']

/-- The `raiseC` span arithmetic: `2k + (L+1) = n+1 ⟹ 2(k+1) + L = (n+1)+1`. -/
private theorem raise_sum_arith {k L n : Nat} (h : 2 * k + (L + 1) = n + 1) :
    2 * (k + 1) + L = n + 1 + 1 := by
  have h' : 2 * k + L + 1 = n + 1 := by rw [Nat.add_assoc]; exact h
  calc 2 * (k + 1) + L = 2 * k + L + 2 := by
            rw [Nat.mul_succ, Nat.add_right_comm (2 * k) 2 L]
    _ = (2 * k + L + 1) + 1 := rfl
    _ = (n + 1) + 1 := by rw [h']

/-- ★ **The symmetric-level invariant.**  `C`'s `cardB` values are the contiguous
    centred run `{k, …, n − k}`: `C.map cardB = [k, …, k + |C| − 1]` and
    `2k + |C| = n + 1`. -/
def SymChain (n : Nat) (C : List (List Bool)) : Prop :=
  ∃ k, C.map cardB = consec k C.length ∧ 2 * k + C.length = n + 1

/-- ★★ **`scd` preserves the symmetric-level invariant** — every chain of `scd n`
    runs symmetrically from some level `k` to `n − k` (length `n − 2k + 1`). -/
theorem scd_sym : ∀ (n : Nat) (C : List (List Bool)), C ∈ scd n → SymChain n C
  | 0, _, h => by
      cases h with
      | head => exact ⟨0, rfl, rfl⟩
      | tail _ h' => nomatch h'
  | n + 1, _, h => by
      obtain ⟨D, hD, hCD⟩ := mem_flatMap213 h
      obtain ⟨k, hmap, hsum⟩ := scd_sym n D hD
      have hDne : D ≠ [] := scd_nonempty n D hD
      rcases mem_scdStep hCD with rfl | rfl
      · -- C = extendC D
        refine ⟨k, ?_, ?_⟩
        · rw [extendC_sym D k hDne hmap, extendC_length D hDne]
        · rw [extendC_length D hDne, ← Nat.add_assoc, hsum]
      · -- C = raiseC D — `raiseC D ≠ []` forces `D = v :: w :: rest`
        cases D with
        | nil => exact absurd rfl hDne
        | cons v ds =>
            cases ds with
            | nil => exact absurd rfl (scd_nonempty (n + 1) (raiseC [v]) h)
            | cons w rest =>
                refine ⟨k + 1, ?_, ?_⟩
                · rw [raiseC_sym v w rest k hmap, raiseC_length v w rest]
                · rw [raiseC_length v w rest]
                  exact raise_sum_arith (L := (w :: rest).length) hsum

/-! ## §11 — the middle layer meets every chain (toward the count `C(n,⌊n/2⌋)`)

The Dilworth **lower** bound is now free: `scd n` is a chain cover (§7), so
`dilworth_lower` gives `C(n,⌊n/2⌋) ≤ |scd n|` (`scd_lower`).  For the matching
**upper** bound we read off the symmetric-level invariant (§10): the run
`[k, …, n−k]` straddles `⌊n/2⌋` (`sym_span`), so every chain contains a
`⌊n/2⌋`-element (`scd_has_middle`) and — being a chain — exactly one
(`scd_middle_unique`).  The injection `chain ↦ middle element` then needs only the
SCD partition-disjointness (the last frontier rung) to give `|scd n| = C(n,⌊n/2⌋)`. -/

/-- `x ∈ [k, …, k+m−1]` whenever `k ≤ x < k + m`. -/
theorem mem_consec : ∀ (k m x : Nat), k ≤ x → x < k + m → x ∈ consec k m
  | k, 0, x, h1, h2 => by rw [Nat.add_zero] at h2; exact absurd h1 (Nat.not_le.2 h2)
  | k, m + 1, x, h1, h2 => by
      show x ∈ k :: consec (k + 1) m
      rcases Nat.eq_or_lt_of_le h1 with heq | hlt
      · rw [← heq]; exact List.Mem.head _
      · have h1' : k + 1 ≤ x := hlt
        have e : (k + 1) + m = k + (m + 1) := by rw [Nat.succ_add, Nat.add_succ]
        have h2' : x < (k + 1) + m := by rw [e]; exact h2
        exact List.Mem.tail _ (mem_consec (k + 1) m x h1' h2')

/-- ★ **The symmetric span.**  A chain with `2k + m = n+1` (`m = |C| ≥ 1`) runs
    from level `k ≤ ⌊n/2⌋` up to level `n − k`, so it straddles the middle. -/
theorem sym_span {n k m : Nat} (h : 2 * k + m = n + 1) (hm : 1 ≤ m) :
    k ≤ half n ∧ k + half n ≤ n := by
  have h2k : 2 * k ≤ n := by
    have hstep : 2 * k + 1 ≤ n + 1 := h ▸ Nat.add_le_add_left hm (2 * k)
    exact Nat.le_of_succ_le_succ hstep
  have hk : k ≤ half n := by
    rcases Nat.lt_or_ge (half n) k with hlt | hge
    · have hmul : 2 * (half n + 1) ≤ 2 * k := Nat.mul_le_mul_left 2 hlt
      rw [Nat.mul_succ] at hmul
      have hbad : 2 * half n + 2 ≤ 2 * half n + 1 :=
        Nat.le_trans (Nat.le_trans hmul h2k) (le_half n)
      exact (Nat.not_succ_le_self (2 * half n + 1) hbad).elim
    · exact hge
  refine ⟨hk, ?_⟩
  have hadd : k + half n ≤ half n + half n := Nat.add_le_add_right hk (half n)
  rw [← Nat.two_mul] at hadd
  exact Nat.le_trans hadd (half_le n)

/-- **Dilworth's lower bound, realised by the SCD.**  `scd n` is a chain cover, so
    `C(n,⌊n/2⌋) ≤ |scd n|` — the SCD attains the Dilworth bound from below. -/
theorem scd_lower (n : Nat) : binom n (half n) ≤ (scd n).length :=
  dilworth_lower (scd n) (scd_isChain n)
    (fun A hA => scd_cover n A (length_of_mem_allBoolLists (mem_filter hA).1))

/-- ★ **Every SCD chain contains a `⌊n/2⌋`-element.**  The symmetric run straddles
    the middle layer (`sym_span` + `mem_consec`). -/
theorem scd_has_middle {n : Nat} {C : List (List Bool)} (hC : C ∈ scd n) :
    ∃ A, A ∈ C ∧ cardB A = half n := by
  obtain ⟨k, hmap, hsum⟩ := scd_sym n C hC
  have hne : C ≠ [] := scd_nonempty n C hC
  have hm : 1 ≤ C.length := by
    cases C with
    | nil => exact absurd rfl hne
    | cons _ _ => exact Nat.succ_le_succ (Nat.zero_le _)
  obtain ⟨hk, hkhalf⟩ := sym_span hsum hm
  have e2 : k + (k + C.length) = n + 1 := by rw [← Nat.add_assoc, ← Nat.two_mul]; exact hsum
  have hlt : half n < k + C.length := by
    have hstep : k + half n + 1 ≤ n + 1 := Nat.succ_le_succ hkhalf
    rw [← e2, Nat.add_assoc] at hstep
    exact E213.Tactic.NatHelper.le_of_add_le_add_left hstep
  have hmem : half n ∈ consec k C.length := mem_consec k C.length (half n) hk hlt
  rw [← hmap] at hmem
  obtain ⟨A, hA, hcard⟩ := exists_of_mem_map hmem
  exact ⟨A, hA, hcard⟩

/-- ★ **At most one `⌊n/2⌋`-element per chain.**  A chain's members have distinct
    sizes (`chain_card_inj`), so the `⌊n/2⌋`-element is unique. -/
theorem scd_middle_unique {n : Nat} {C : List (List Bool)} (hC : C ∈ scd n)
    {A B : List Bool} (hA : A ∈ C) (hB : B ∈ C)
    (hcA : cardB A = half n) (hcB : cardB B = half n) : A = B :=
  chain_card_inj (scd_isChain n C hC A hA B hB) (hcA.trans hcB.symm)

/-! ## §12 — nodup infrastructure (chains have no repeats)

The `cardB` run `consec k m` is strictly increasing, hence duplicate-free
(`consec_nodup`); a chain's `cardB` map being nodup forces the chain itself nodup
(`nodup_of_nodup_map`), so every SCD chain is duplicate-free (`scd_chain_nodup`). -/

/-- Every member of the run `[k,…,k+m−1]` is `≥ k`. -/
theorem mem_consec_lb : ∀ (k m x : Nat), x ∈ consec k m → k ≤ x
  | _, 0, _, h => nomatch h
  | k, m + 1, x, h => by
      cases h with
      | head => exact Nat.le_refl k
      | tail _ h' => exact Nat.le_of_succ_le (mem_consec_lb (k + 1) m x h')

/-- The consecutive run is duplicate-free. -/
theorem consec_nodup : ∀ (k m : Nat), (consec k m).Nodup
  | _, 0 => List.Pairwise.nil
  | k, m + 1 => by
      show (k :: consec (k + 1) m).Nodup
      refine List.Pairwise.cons ?_ (consec_nodup (k + 1) m)
      intro b hb heq
      rw [← heq] at hb
      exact Nat.not_succ_le_self k (mem_consec_lb (k + 1) m k hb)

/-- A nodup image forces a nodup source. -/
theorem nodup_of_nodup_map {α β : Type _} (g : α → β) :
    ∀ {C : List α}, (C.map g).Nodup → C.Nodup
  | [], _ => List.Pairwise.nil
  | a :: l, h => by
      cases h with
      | cons hh ht =>
          refine List.Pairwise.cons ?_ (nodup_of_nodup_map g ht)
          intro b hb heq
          exact hh (g b) (mem_map_of_mem g hb) (congrArg g heq)

/-- ★ **Every SCD chain is duplicate-free.**  Its `cardB` values are the strictly
    increasing run `consec k |C|`, which has no repeats. -/
theorem scd_chain_nodup {n : Nat} {C : List (List Bool)} (hC : C ∈ scd n) : C.Nodup := by
  obtain ⟨k, hmap, _⟩ := scd_sym n C hC
  refine nodup_of_nodup_map cardB ?_
  rw [hmap]; exact consec_nodup k C.length

end E213.Lib.Math.Combinatorics.ChainAntichain
