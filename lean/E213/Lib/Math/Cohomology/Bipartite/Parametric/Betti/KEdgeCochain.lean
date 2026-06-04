import E213.Lib.Math.Cohomology.Bipartite.Parametric.Betti.PathCoboundary

/-!
# K_{NS,NT} edge cochain — `|im δ⁰_K| = 2^(V−1)` wired to the actual coboundary

`PathCoboundary.im_count_inj_complement` proves `|im f| = 2^(V−1)` for any
complement-invariant, head-`false`-injective map.  This file instantiates
it at the genuine complete-bipartite coboundary `edgeCochain`, so the b₁
image count is about K_{NS,NT}'s own δ⁰, not a connectivity proxy.

`edgeCochain NS NT σ` is the list of edge values `σ[s] ⊕ σ[NS+t]` over all
`(s, t)` with `s < NS`, `t < NT` (the `c` parallel-edge copies do not
change the image, so the `c = 1` edge set is used; `|im|` is `c`-independent).
The two hypotheses are proven directly on the list representation:

  - `edgeCochain_complement` — complement-invariance (`(¬a) ⊕ (¬b) = a ⊕ b`);
  - `edgeCochain_inj_headFalse` — injective on head-`false` colourings:
    equal edge values force the difference `σ ⊕ τ` constant across the
    complete-bipartite adjacency (connectedness), and head-`false` pins it
    to all-`false`, so `σ = τ`.

No `funext`, `Fintype`, or `Nat.div`.

Companion: `theory/math/cohomology/bipartite.md`.
-/

namespace E213.Lib.Math.Cohomology.Bipartite.Parametric.Betti.KEdgeCochain

open E213.Lib.Math.Combinatorics.BoolEnum
  (allBoolLists complement headFalse length_of_mem_allBoolLists mem_allBoolLists)
open E213.Tactic.List213
  (mem_append_left mem_append_right mem_append_iff mem_map_of_mem exists_of_mem_map
   mem_flatMap_intro mem_flatMap_elim getD_map_ib map_congr map_eq_comp list_ext_getD getD_ge)
open E213.Lib.Math.Cohomology.Bipartite.Parametric.Betti.PathCoboundary (im_count_inj_complement)

/-! ## Index enumeration

Generic ∅-axiom `List` helpers (`mem_*`, `flatMap`, `getD`, `map_eq_comp`,
`list_ext_getD`) live in `Meta.Tactic.List213`; this file keeps the
`rangeL` index enumeration and the edge cochain. -/

/-- `[0, 1, …, n−1]` (own definition — core `List.range` membership lemmas
    carry `propext` / `Quot.sound`). -/
def rangeL : Nat → List Nat
  | 0 => []
  | n + 1 => rangeL n ++ [n]

/-- `i < n → i ∈ rangeL n`. -/
theorem mem_rangeL : ∀ {n i : Nat}, i < n → i ∈ rangeL n
  | n + 1, i, h => by
      show i ∈ rangeL n ++ [n]
      rcases Nat.lt_or_ge i n with hlt | hge
      · exact mem_append_left (mem_rangeL hlt)
      · -- i = n
        have : i = n := Nat.le_antisymm (Nat.le_of_lt_succ h) hge
        exact mem_append_right _ (this ▸ List.Mem.head _)

/-! ## The edge cochain -/

/-- All `(s, t)` index pairs with `s < NS`, `t < NT`. -/
def edgePairs (NS NT : Nat) : List (Nat × Nat) :=
  (rangeL NS).flatMap (fun s => (rangeL NT).map (fun t => (s, t)))

/-- `(s, t)` with `s < NS`, `t < NT` is an edge pair. -/
theorem mem_edgePairs {NS NT s t : Nat} (hs : s < NS) (ht : t < NT) :
    (s, t) ∈ edgePairs NS NT :=
  mem_flatMap_intro (mem_rangeL hs)
    (mem_map_of_mem (fun t => (s, t)) (mem_rangeL ht))

/-- Value of edge `(s, t)`: `σ[s] ⊕ σ[NS+t]`. -/
def edgeVal (NS : Nat) (σ : List Bool) (st : Nat × Nat) : Bool :=
  xor (σ.getD st.1 false) (σ.getD (NS + st.2) false)

/-- The complete-bipartite (`c = 1`) coboundary as a list of edge values. -/
def edgeCochain (NS NT : Nat) (σ : List Bool) : List Bool :=
  (edgePairs NS NT).map (edgeVal NS σ)

/-! ## Complement invariance -/

/-- `(complement σ).getD i false = (σ.getD i false == false)` in bounds. -/
private theorem complement_getD {σ : List Bool} {i : Nat} (h : i < σ.length) :
    (complement σ).getD i false = (σ.getD i false == false) :=
  getD_map_ib (· == false) false false σ i h

/-- `i ∈ rangeL n → i < n`. -/
theorem lt_of_mem_rangeL : ∀ {n i : Nat}, i ∈ rangeL n → i < n
  | n + 1, i, h => by
      rcases mem_append_iff (show i ∈ rangeL n ++ [n] from h) with h' | h'
      · exact Nat.lt_succ_of_lt (lt_of_mem_rangeL h')
      · cases h' with
        | head => exact Nat.lt_succ_self n
        | tail _ h'' => nomatch h''

/-- Edge-pair membership elimination. -/
theorem lt_of_mem_edgePairs {NS NT : Nat} {st : Nat × Nat} (h : st ∈ edgePairs NS NT) :
    st.1 < NS ∧ st.2 < NT := by
  rcases mem_flatMap_elim h with ⟨s, hs, hst⟩
  rcases exists_of_mem_map hst with ⟨t, ht, heq⟩
  rw [← heq]
  exact ⟨lt_of_mem_rangeL hs, lt_of_mem_rangeL ht⟩

/-! ## Complement invariance -/

/-- `xor` of two negations is the original `xor`. -/
private theorem xor_not_not (a b : Bool) : xor (a == false) (b == false) = xor a b := by
  cases a <;> cases b <;> rfl

/-- **Complement invariance** on length-`(NS+NT)` colourings. -/
theorem edgeCochain_complement (NS NT : Nat) {σ : List Bool}
    (hσ : σ.length = NS + NT) :
    edgeCochain NS NT (complement σ) = edgeCochain NS NT σ := by
  refine map_congr (fun st hst => ?_)
  obtain ⟨hs, ht⟩ := lt_of_mem_edgePairs hst
  have h1 : st.1 < σ.length := by rw [hσ]; exact Nat.lt_of_lt_of_le hs (Nat.le_add_right NS NT)
  have h2 : NS + st.2 < σ.length := by rw [hσ]; exact Nat.add_lt_add_left ht NS
  show xor ((complement σ).getD st.1 false) ((complement σ).getD (NS + st.2) false)
        = xor (σ.getD st.1 false) (σ.getD (NS + st.2) false)
  rw [complement_getD h1, complement_getD h2, xor_not_not]

/-! ## Head-`false` injectivity (reconstruction) -/

/-- A head-`false` colouring has `getD 0 = false`. -/
private theorem headFalse_getD0 : ∀ {σ : List Bool}, headFalse σ = true →
    σ.getD 0 false = false
  | [], h => Bool.noConfusion h
  | false :: _, _ => rfl
  | true :: _, h => Bool.noConfusion h

/-- `xor a b = xor c d → xor a c = xor b d`. -/
private theorem xor_swap {a b c d : Bool} (h : xor a b = xor c d) :
    xor a c = xor b d := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    first | rfl | exact Bool.noConfusion h

/-- `xor a b = false → a = b`. -/
private theorem eq_of_xor_false {a b : Bool} (h : xor a b = false) : a = b := by
  cases a <;> cases b <;> first | rfl | exact Bool.noConfusion h

/-- **Injective on head-`false` colourings.**  Equal edge values force the
    difference `σ ⊕ τ` constant across the complete-bipartite adjacency;
    head-`false` pins it to all-`false`, so `σ = τ`. -/
theorem edgeCochain_inj_headFalse (NS NT : Nat) (hNS : 0 < NS) (hNT : 0 < NT)
    {σ τ : List Bool} (hσl : σ.length = NS + NT) (hτl : τ.length = NS + NT)
    (hσh : headFalse σ = true) (hτh : headFalse τ = true)
    (he : edgeCochain NS NT σ = edgeCochain NS NT τ) : σ = τ := by
  -- per-edge equality
  have hedge : ∀ s t, s < NS → t < NT →
      xor (σ.getD s false) (σ.getD (NS + t) false)
        = xor (τ.getD s false) (τ.getD (NS + t) false) :=
    fun s t hs ht => map_eq_comp he (s, t) (mem_edgePairs hs ht)
  -- difference at vertex 0 is false
  have hd0 : xor (σ.getD 0 false) (τ.getD 0 false) = false := by
    rw [headFalse_getD0 hσh, headFalse_getD0 hτh]; rfl
  -- the difference is constant on every vertex < NS + NT
  have key : ∀ i, i < NS + NT → xor (σ.getD i false) (τ.getD i false) = false := by
    intro i hi
    rcases Nat.lt_or_ge i NS with hlt | hge
    · have e1 := xor_swap (hedge i 0 hlt hNT)
      have e2 := xor_swap (hedge 0 0 hNS hNT)
      rw [e1, ← e2]; exact hd0
    · rcases Nat.le.dest hge with ⟨k, hk⟩
      have hkNT : k < NT := by
        have : NS + k < NS + NT := by rw [hk]; exact hi
        exact Nat.lt_of_add_lt_add_left this
      have e1 := xor_swap (hedge 0 k hNS hkNT)
      rw [hk] at e1
      rw [← e1]; exact hd0
  -- list extensionality
  refine list_ext_getD false (hσl.trans hτl.symm) (fun i => ?_)
  rcases Nat.lt_or_ge i (NS + NT) with hi | hi
  · exact eq_of_xor_false (key i hi)
  · rw [getD_ge false (hσl ▸ hi), getD_ge false (hτl ▸ hi)]

/-! ## Application: `|im δ⁰_K| = 2^(V−1)` -/

/-- ★★★★★★ **The complete-bipartite coboundary's image has cardinality
    `2^(V−1)`.**  Instantiates `im_count_inj_complement` at the genuine
    `edgeCochain NS NT` (complement-invariant + head-`false`-injective). -/
theorem im_edgeCochain_card (NS NT n : Nat) (hNS : 0 < NS) (hNT : 0 < NT)
    (hV : NS + NT = n + 1) :
    (((allBoolLists (n + 1)).filter headFalse).map (edgeCochain NS NT)).Nodup
    ∧ (((allBoolLists (n + 1)).filter headFalse).map (edgeCochain NS NT)).length = 2 ^ n
    ∧ ∀ σ, σ ∈ allBoolLists (n + 1) →
        edgeCochain NS NT σ ∈
          ((allBoolLists (n + 1)).filter headFalse).map (edgeCochain NS NT) :=
  im_count_inj_complement n (edgeCochain NS NT)
    (fun l hl => edgeCochain_complement NS NT
      (by rw [length_of_mem_allBoolLists hl, hV]))
    (fun ρ μ hρ hμ hρh hμh he =>
      edgeCochain_inj_headFalse NS NT hNS hNT
        (by rw [length_of_mem_allBoolLists hρ, hV])
        (by rw [length_of_mem_allBoolLists hμ, hV]) hρh hμh he)

/-- For the forced `K_{3,2}^{(c=2)}`: the (c=1) edge cochain image has
    `2^4 = 16` values, i.e. `dim im δ⁰ = 4 = V − 1`. -/
theorem im_edgeCochain_K32 :
    (((allBoolLists 5).filter headFalse).map (edgeCochain 3 2)).length = 2 ^ 4 :=
  (im_edgeCochain_card 3 2 4 (by decide) (by decide) (by decide)).2.1

end E213.Lib.Math.Cohomology.Bipartite.Parametric.Betti.KEdgeCochain
