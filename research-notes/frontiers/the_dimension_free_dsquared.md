# Frontier — the dimension-free `δ² = 0`

**Status**: open.  The one genuinely-hard core of the 213-native ℤ/2 cochain
complex; everything around it is closed.

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

   **Still open — the parity accounting only.**  With every structural fact
   closed, the remaining step is pure XOR bookkeeping: (i) rewrite `δ²σ(τ)` (a
   nested `foldl`-XOR) as a flat XOR over the `(a,b)` grid, using the round-trip
   to collapse the inner `subsetIdx ∘ eraseIdx ∘ kSubset` to the genuine face;
   (ii) an abstract **involution-cancellation** lemma — a XOR-fold over a `Nodup`
   list with a fixed-point-free, summand-preserving involution is `false` — applied
   to the grid via `eraseIdx_eraseIdx_comm`.  No new structural facts are needed;
   it is the combinatorial accounting Mathlib hides inside
   `AlternatingFaceMapComplex`, here owed over the brute-force `foldl`.

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
- **Closed (this session, §6)**: `sorted_eraseIdx` (faces stay `Sorted`) and
  `eraseIdx_eraseIdx_comm` (the simplicial commutation identity = the involution
  kernel).  **All structural lemmas for `δ²=0` are now machine-verified PURE.**
- **Next — the only remaining gap**: the XOR-parity accounting (flatten the nested
  `δ²` fold via the round-trip + an abstract involution-cancellation lemma applied
  through `eraseIdx_eraseIdx_comm`).  No new structural facts required.  Then
  `delta_sq_zero_general`.

## Cross-refs

- `lean/E213/Lib/Math/Cohomology/Examples/ColexRoundTrip.lean` — the colex round-trip core (this session).
- `lean/E213/Lib/Math/Cohomology/ChainComplex.lean` — the closed atomic capstone.
- `lean/E213/Lib/Math/Cohomology/Delta/{Core,Linear,Pointwise,SqZero}.lean`.
- `lean/E213/Lib/Math/Cohomology/Universal/Prop*.lean` — per-dimension lifts.
- `research-notes/frontiers/the_one_act.md` — the seminar that named the tower.
