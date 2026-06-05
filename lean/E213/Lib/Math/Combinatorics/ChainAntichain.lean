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
   kLayer kLayer_isAntichain half kLayer_card kLayer_nodup)
open E213.Lib.Math.Combinatorics.SpernerChains
  (idxList idxList_length idxList_nodup mem_idxList_lt cardB_le_length
   beqBoolList beqBoolList_refl eq_of_beqBoolList)
open E213.Lib.Math.Combinatorics.BoolEnum (mem_allBoolLists)
open E213.Lib.Physics.Simplex.Counts (binom)
open E213.Tactic.List213
  (mem_append_left mem_append_right exists_of_mem_map mem_map_of_mem nodup_map_of_inj
   nodup_length_le_of_subset length_map mem_filter_of mem_filter)

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

open E213.Lib.Math.Combinatorics.Permutations (flatMap213 mem_flatMap213 mem_flatMap213_of)

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

end E213.Lib.Math.Combinatorics.ChainAntichain
