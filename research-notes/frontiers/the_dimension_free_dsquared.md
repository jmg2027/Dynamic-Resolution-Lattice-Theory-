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

## Proof strategy (the two missing lemmas)

`kSubset` is a colex recursion on `n` (`Examples/SimplexBasis.lean`):

```
kSubset (n+1) (k+1) i = if i < binom n (k+1) then kSubset n (k+1) i
                        else kSubset n k (i - binom n (k+1)) ++ [n]
```

1. **Colex round-trip** — `subsetIdx n k (kSubset n k i) = i` for `i < binom n k`,
   and `kSubset n k (subsetIdx n k s) = s` for a strictly-increasing `s` with
   entries `< n`.  By induction on `n` against the Pascal split.  This is what
   lets `delta`'s inner `subsetIdx ∘ … ∘ kSubset` round-trip back to a genuine
   face, so the two deltas compose as face-removals rather than as opaque index
   arithmetic.  (Currently only the concrete `RoundTrip.round_trip_5_k` exist.)

2. **The 2-to-1 face pairing** — a fixed-point-free involution on
   `{(a,b) : a ∈ range (k+2), b ∈ range (k+1)}` that preserves the resulting
   face `(τ.eraseIdx a).eraseIdx b`.  Concretely the order-swap on the two removed
   positions:  `(τ.eraseIdx a).eraseIdx b = (τ.eraseIdx a').eraseIdx b'` where
   `(a',b')` removes the same two vertices in the opposite order.  Paired with
   `xor_self_eq_false` and a foldl-over-pairs regrouping (the multiset of face
   indices has every element even), this gives `δ²σ(τ) = false`.

Both ∅-axiom: structural induction + `eraseIdx`/`List` lemmas + `Eq.subst`/`▸`,
no funext (use the `Delta.Pointwise` pattern), no `decide` over the function
space.  The hard part is (2)'s index bookkeeping over `eraseIdx` on the sorted
colex list — exactly the work Mathlib hides inside `AlternatingFaceMapComplex`,
here owed in the brute-force colex representation.

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

## Cross-refs

- `lean/E213/Lib/Math/Cohomology/ChainComplex.lean` — the closed atomic capstone.
- `lean/E213/Lib/Math/Cohomology/Delta/{Core,Linear,Pointwise,SqZero}.lean`.
- `lean/E213/Lib/Math/Cohomology/Universal/Prop*.lean` — per-dimension lifts.
- `research-notes/frontiers/the_one_act.md` — the seminar that named the tower.
