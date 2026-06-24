# Frontier — the dimension-free `δ² = 0`

**Status**: ✅ **CLOSED** (`lean/E213/Lib/Math/Cohomology/DeltaSqZero.lean`).
`delta_sq_zero_general : ∀ {n k} (σ : Cochain n k) (τ : Fin (binom n (k+2))),
delta (delta σ) τ = false` — `#print axioms` reports **no axioms**.  The genuine
chain-complex law, uniform in the dimension `n` and degree `k`, ∅-axiom, no
`decide`/Fintype.

## How it closed

`δ²σ(τ)` unfolds — twice `DeltaSqZero.deltaAt_eq_xorFold` (reading `σ` through
`cochainAtNat`, `false` out of range, so `deltaAt`'s dependent-`if` `foldl`
becomes a guard-free `xorFold`), with the colex bijection (`kSubset_subsetIdx` +
the face-validity lemmas `kSubset_sorted`/`sorted_eraseIdx`/`subsetIdx_lt`)
collapsing the inner `kSubset ∘ subsetIdx` to the genuine double-erase face — to
a single `xorFold` over the `(k+2)×(k+1)` removal grid (`gridList`,
`xorFold_gridList`).  The order-swap involution `gridInv : (a,b) ↦ (b+1,a)` for
`a ≤ b` is fixed-point-free and preserves the summand (the two removal orders hit
the same face, `eraseIdx_eraseIdx_comm`), so `xorFold_involution` cancels every
value in pairs (`grid_xorFold_zero`).  The whole chain is `∅`-axiom.

This is exactly the work Mathlib hides inside `AlternatingFaceMapComplex`, here
owned from scratch over the brute-force colex `foldl` representation.

## Remaining (a *different*, deeper frontier)

The **Cantor / re-entry coker** unification (`the_one_act.md`) — exhibiting the
diagonal residue (`Object1`) as the cohomology of an honest 213-native complex —
is a separate open problem, not this one.  `δ²=0` for the simplicial complex is
done.

---

## (historical) What was closed before the finish

## What is closed

The simplicial cochain complex is real and ∅-axiom
(`lean/E213/Lib/Math/Cohomology/`):

- `Cochain n k = Fin (binom n k) → Bool` — k-cochains on Δⁿ⁻¹, mod-2
  (`Cochain/Core.lean`).
- `delta : Cochain n k → Cochain n (k+1)` — the colex coboundary, XOR over the
  faces of each (k+1)-subset (`Delta/Core.lean`).
- `Delta.Linear.delta_add` — `δ(σ+τ) = δσ + δτ`, **universal in `(n,k)`**.  `δ`
  is a graded ℤ/2-linear differential.
- `δ² = 0` for **every** cochain at **every** degree of the atomic simplex Δ⁴
  (`Universal.Prop.dsq_zero_prop_5_0`, `Prop51`–`Prop53`), plus Δ⁵ vertex
  cochains (`Prop61`).  Assembled as `ChainComplex.atomic_chain_complex`.
- Acyclicity at Δ⁴: reduced ℤ/2 Betti `b̃₀ = b̃₁ = 0` (`Examples.BettiKernel`).

The closed-degree route is a Bool-pattern `decide` lifted to `∀ σ` through the
funext-free `Delta.Pointwise.delta_pointwise_eq`.  It is **per fixed `(n,k)`**:
the pattern hard-codes `binom n k` Bool slots and `decide` enumerates the
`2^(binom n k)` cochains.  Nothing in it is uniform in `n`.

## The open theorem

```lean
theorem delta_sq_zero_general :
    ∀ {n k : Nat} (σ : Cochain n k) (i : Fin (binom n (k + 2))),
      delta (delta σ) i = false
```

Uniform in the dimension `n` and degree `k`.  `decide` cannot reach it: core
Lean has no `Fintype`/`DecidablePred` on `Cochain n k = Fin (binom n k) → Bool`,
and no finite enumeration is uniform in `n`.  It needs the **simplicial pairing
identity**, proved structurally.

## Why it is true (the mod-2 cancellation)

`delta (delta σ) τ` for a (k+2)-subset `τ` is, unfolding `deltaAt` twice, an XOR
over ordered pairs `(a, b)` with `a ∈ range (k+2)`, `b ∈ range (k+1)`:

    δ²σ(τ) = XOR_{a,b} σ( (τ.eraseIdx a).eraseIdx b )

Each k-subset face of `τ` is `τ` with **two** vertices removed.  The two removal
*orders* of the same unordered vertex-pair `{p, q}` (remove the larger-index
position first, or the smaller first) hit the *same* face.  So every face index
appears in the XOR an **even** number of times (exactly twice), and
`xor b b = false` (`Cochain.Core.xor_self_eq_false`) collapses the whole sum to
`false` — independent of `σ`'s values.  This is the classical `d_i d_j = d_{j-1}
d_i` (for `i < j`) face identity, in mod-2 colex-index form.

## Proof strategy (the missing lemmas)

`kSubset` is a colex recursion on `n` (`Examples/SimplexBasis.lean`):

```
kSubset (n+1) (k+1) i = if i < binom n (k+1) then kSubset n (k+1) i
                        else kSubset n k (i - binom n (k+1)) ++ [n]
```

1. **Colex round-trip** — `subsetIdx n k (kSubset n k i) = i` for `i < binom n k`,
   and `kSubset n k (subsetIdx n k s) = s` for a strictly-increasing `s` with
   entries `< n`.  This is what lets `delta`'s inner `subsetIdx ∘ … ∘ kSubset`
   round-trip back to a genuine face, so the two deltas compose as face-removals
   rather than as opaque index arithmetic.

   **DONE (this session)** — `Examples/ColexRoundTrip.lean`, all ∅-axiom, uniform
   in `(n,k)`:
   - `kSubset_mem_lt` — every entry of `kSubset n k i` is `< n`;
   - `kSubset_length` — `kSubset n k i` has length `k` (for `i < binom n k`);
   - `kSubset_inj` — `kSubset n k` is **injective** on `{0..binom n k − 1}` (the
     key combinatorial fact: the cross case is killed because the at-or-above
     subset contains vertex `n`, which `kSubset_mem_lt` forbids in the below one);
   - `subsetIdx_kSubset` — the **forward round-trip** `subsetIdx n k (kSubset n k
     i) = i`, via `kSubset_inj` + a hand-built pure `find?`/`List.range`/`BEq`
     layer (the core `List.range`/`find?`/`LawfulBEq (List Nat)` lemmas all leak
     `propext`/`Quot.sound`, so they are rebuilt from `find?_cons` + the
     `instBEqOfDecidableEq` reduction).
   - `Sorted` (strictly-increasing predicate) + `sorted_append_singleton` +
     `sorted_snoc_decomp` (peel the strict-max last element);
   - `kSubset_surj` — **surjectivity**: every `Sorted` list of length `k` with
     entries `< n` is `kSubset n k j` for some `j < binom n k` (induction on `n`,
     split on whether the last element is `n`);
   - `kSubset_subsetIdx` — the **reverse round-trip** `kSubset n k (subsetIdx n k
     s) = s` for a `Sorted` in-range length-`k` list (surjectivity + forward).

   **Both round-trip directions are now closed** (`kSubset`/`subsetIdx` are a
   genuine bijection between `{0..binom n k − 1}` and the sorted k-subsets).

2. **The 2-to-1 face pairing** — a fixed-point-free involution on
   `{(a,b) : a ∈ range (k+2), b ∈ range (k+1)}` that preserves the resulting
   face `(τ.eraseIdx a).eraseIdx b`.

   **DONE (this session)** — the structural kernel, `ColexRoundTrip.lean §6`:
   - `sorted_eraseIdx` — erasing a vertex from a `Sorted` colex subset keeps it
     `Sorted` (so every face round-trips via `kSubset_subsetIdx`);
   - `eraseIdx_eraseIdx_comm` — the **simplicial commutation identity**
     `(L.eraseIdx i).eraseIdx j = (L.eraseIdx (j+1)).eraseIdx i` for `i ≤ j`
     (the `d_i d_j = d_{j-1} d_i` face identity in index form).  This *is* the
     involution kernel: `(a,b) ↦ (b+1, a)` for `a ≤ b` sends `(τ.eraseIdx
     a).eraseIdx b` to the same face by the opposite removal order.

   **The abstract engine is now DONE** (`Examples/XorInvolution.lean`,
   `xorFold_involution`, PURE): a ℤ/2 XOR-fold over a `Nodup` list is `false`
   whenever the index set carries a **fixed-point-free, summand-preserving
   involution** (proof: strong induction peeling a matched pair `{x, g x}` per
   step via `List.filter`, cancelling `f x ⊕ f (g x) = false`).  This is "a
   fixed-point-free involution ⟹ even cardinality" in XOR form — the colex-
   independent keystone.

   **The guard is now handled** (`DeltaSqZero.lean`, PURE): `deltaAt_eq_xorFold` —
   reading `σ` through `cochainAtNat` (`false` out of range) collapses `deltaAt`'s
   dependent-`if` `foldl` to an unconditional `xorFold` over the faces.  In range it
   is the real `σ`-value; out of range `xor acc false = acc`, exactly the `else`
   branch — so the guard vanishes with no validity hypothesis.  Plus the two guard-
   discharge lemmas `kSubset_sorted` + `subsetIdx_lt` (`ColexRoundTrip`).

   **Still open — the final assembly only** (mechanical, no new structural/abstract
   facts): (i) compose two `deltaAt_eq_xorFold` rewrites for `δ²`, inserting the
   reverse round-trip `kSubset_subsetIdx` (faces valid via `sorted_eraseIdx` +
   `kSubset_sorted` + `length_eraseIdx_of_lt`) to collapse the inner `kSubset ∘
   subsetIdx` to the genuine double-erase face; (ii) flatten the nested `xorFold`
   over `(a,b)` to a `xorFold` over the grid list (pure `flatMap`/`Nodup`); (iii)
   supply the involution `(a,b) ↦ (b+1,a)` for `a ≤ b` and discharge its four
   hypotheses via `eraseIdx_eraseIdx_comm` (summand-preservation) + index arithmetic,
   then apply `xorFold_involution`.

All ∅-axiom: structural induction + `eraseIdx`/`List` lemmas + `Eq.subst`/`▸`,
no funext (use the `Delta.Pointwise` pattern), no `decide` over the function space.

## Relation to the other residue / coker

Do **not** conflate this complex's cohomology with the Cantor residue
(`the_one_act.md` Homology verdict, now corrected).  Two distinct cokernels:

- **Simplicial**: `H^k = ker δ / im δ` of *this* complex — finite, geometric,
  the Betti numbers (`coker δ`, `BettiKernel`).  `δ²=0` is its defining law.
- **Cantor / re-entry**: `coker(Object1)` and `coker(Object1 ∘ predicateToRaw n)`
  (`FlatOntologyClosure`, `ResidueReentry.graded_residue_tower`) — the
  diagonal/definability gap, a *different* object (`Raw → Bool`, not `Fin (binom
  n k) → Bool`).

`Bridge/PredicateAsCochain.lean` reads a predicate as a 1-cochain (`rfl`), which
is suggestive but **not** an identification of the two cokers.  Unifying them —
exhibiting the Cantor residue as the cohomology of an honest 213-native complex
with a real `δ²=0` differential — is a *second*, deeper open frontier, distinct
from `delta_sq_zero_general` above.

## Progress ledger

- **Closed**: the **full colex bijection** (`ColexRoundTrip.lean`, all ∅-axiom) —
  `kSubset_mem_lt`, `kSubset_length`, `kSubset_inj`, `subsetIdx_kSubset` (forward),
  `kSubset_surj` (surjectivity), `kSubset_subsetIdx` (reverse).  `kSubset`/`subsetIdx`
  are inverse on `{0..binom n k − 1}` ↔ sorted k-subsets.
- **Closed (§6)**: `sorted_eraseIdx` + `eraseIdx_eraseIdx_comm` (the simplicial
  commutation identity = the involution kernel).
- **Closed (`XorInvolution.lean`)**: `xorFold_involution` — the abstract
  fixed-point-free-involution ⟹ XOR-fold = `false` engine (PURE, colex-independent).
- **Next — the only remaining gap**: the *application* — express `δ²σ(τ)` as a
  `xorFold` over the `(a,b)` grid (round-trip to collapse the faces, handle the
  `deltaAt` `if`-guard) and feed the `(a,b) ↦ (b+1,a)` involution into
  `xorFold_involution`.  No new structural or abstract facts required.  Then
  `delta_sq_zero_general`.

## Cross-refs

- `lean/E213/Lib/Math/Cohomology/Examples/ColexRoundTrip.lean` — the colex round-trip core (this session).
- `lean/E213/Lib/Math/Cohomology/ChainComplex.lean` — the closed atomic capstone.
- `lean/E213/Lib/Math/Cohomology/Delta/{Core,Linear,Pointwise,SqZero}.lean`.
- `lean/E213/Lib/Math/Cohomology/Universal/Prop*.lean` — per-dimension lifts.
- `research-notes/frontiers/the_one_act.md` — the seminar that named the tower.
