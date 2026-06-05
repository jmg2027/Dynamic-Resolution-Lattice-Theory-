# Why Sperner's theorem works — the largest antichain, compiled

**Reproduced result.** Sperner (1928): the largest *antichain* in the Boolean
lattice `2^[n]` — a family of subsets, none containing another — has size
`C(n, ⌊n/2⌋)`, the largest binomial in row `n`.

**Why we picked it.** The probabilistic method (`probabilistic_method.md`)
compiled to **COUNT** through the *union bound*: bad events cover few colourings,
so a good one is left over.  Sperner's upper bound compiles to the **dual** of
that same move — the **double count** — and reproducing it tests whether the
dual is a new instruction or the same `COUNT` read from the other side.  The
answer is the latter, and saying *why* is the content: the union bound and the
LYM inequality are **one 0/1 incidence matrix, summed by rows versus by
columns**.

Sperner's number and its bound are two separate ISA moves, and separating them
is the lesson.

## The number is a READ ∘ unimodality, not a count of antichains

*Why `C(n,⌊n/2⌋)`?*  Not because antichains were enumerated — because the
**layers** were read and compared.

  - **READ.** The `k`-th layer's size is a count-Lens reading of the residue,
    and the reading *is* Pascal's recursion: a length-`(n+1)` subset either omits
    the new point (a size-`k` subset of the first `n`) or includes it (a
    size-`(k−1)` one), so `layer(n+1,k) = layer(n,k−1) + layer(n,k)` — the
    binomial recursion, on the nose.
    `layer_size : bcount (cardEq k) (allBoolLists n) = binom n k` (∅-axiom).
  - **Unimodality.** Among the `n+1` layers the middle is the largest. The engine
    is the **absorption identity** `(k+1)·C(n,k+1) = (n−k)·C(n,k)` — Pascal's
    *multiplicative* shadow — whose ratio `(n−k)/(k+1)` crosses `1` exactly at
    `k = ⌊n/2⌋`.
    `absorb`, `binom_mono_up`, `binom_mono_down`, `binom_le_binom_mid` (∅-axiom).

So `C(n,⌊n/2⌋)` is *derived as the largest layer*, not asserted as the answer.
That the bound is **achieved** is the same READ run forward: the middle layer is
itself an antichain (next section), of size `binom n ⌊n/2⌋` — `lower_bound`.

## The antichain is a SEPARATE

Equal-size distinct subsets are **incomparable**: if `A ⊆ B` and `|A| = |B|`
then `A = B`.  This is the `SEPARATE` instruction — the inclusion reading
collapses a size-layer to its diagonal, separating any two distinct members.
`eq_of_subseteq_card_eq` (∅-axiom).  Hence *any* sub-family of one layer is
automatically an antichain, and the bound for such **uniform** antichains is
immediate and fully general: a single-layer antichain is bounded by its layer,
and no layer beats the middle.
`uniform_antichain_le : L.Nodup → (∀A∈L, |A|=k) → |L| ≤ binom n ⌊n/2⌋` (∅-axiom).

The whole difficulty of Sperner is the *cross-layer* claim: mixing sizes cannot
beat the single best layer.  That is LYM.

## The upper bound is the double count — the dual of the union bound

Build the 0/1 **incidence matrix** `inc A c` = "subset `A` lies on maximal chain
`c`" (a chain = a saturated `∅ ⊂ … ⊂ [n]`, i.e. an ordering of the `n` points).
Two facts:

  - **each chain meets the antichain at most once** — a chain is totally ordered,
    an antichain has no two comparable members, so a chain contains ≤ 1 of them
    (`lcount (fun A => inc A c) F ≤ 1`);
  - **read the matrix two ways.** Summed by rows: `Σ_{A∈F}` (chains through `A`).
    Summed by columns: `Σ_{c}` (members on `c`) `≤ Σ_c 1 = #chains`.

The double sum is one number; the column reading bounds it.  *This is the engine*,
and it is exactly the union bound's mirror — there, the matrix (bad-event × point)
is summed to over-count coverage for an *upper* bound on the bad set; here it is
summed to bound the antichain.  Both are Fubini on a finite 0/1 residue:

```
sumOver_swap     : Σ_A Σ_c g A c = Σ_c Σ_A g A c            (the swap = the matrix's two readings)
lym_double_count : (∀ c, #members-on-c ≤ 1) → Σ_A #chains-through-A ≤ #chains
```

(`lym_double_count`, ∅-axiom.)  The "≤ 1 per column" hypothesis is the antichain
property; the conclusion is LYM in integer form.  Dividing by `#chains` recovers
the familiar `Σ_{A∈F} 1/C(n,|A|) ≤ 1`, and since every `C(n,|A|) ≤ C(n,⌊n/2⌋)`
(unimodality), `|F| ≤ C(n,⌊n/2⌋)`.

**The answer to "why".** Sperner did not enumerate antichains. He read *one*
finite incidence residue (subsets × chains) by rows and by columns, and the
column reading — one member per chain — bounds the row reading. The primitive
doing the work is the **double count**: a single residue cardinality is two
sums, and bounding either bounds the other. It is the `COUNT` instruction's
other face — `pigeonhole`/union-bound is *deficit ⟹ existence*; LYM is
*per-column cap ⟹ row-sum bound* — the same `GAP`-by-cardinality, mirrored.

## Compiled form

```
|antichain(2^[n])| ≤ C(n,⌊n/2⌋)
  = double-COUNT      (the incidence matrix, two readings ; lym_double_count ∘ sumOver_swap)
  ∘ SEPARATE          (≤ 1 per chain = antichain incomparability ; eq_of_subseteq_card_eq)
  ∘ READ ∘ unimodality(the layers are binomials, middle largest ; layer_size, binom_le_binom_mid)
```

## The named bound, closed (the rung discharged)

The engine is general; the *named* bound needs the chain model's two counts —
and both are now built ∅-axiom, so Sperner's named upper bound holds
**unconditionally** (`SpernerChains.sperner`, `sperner_theorem`):

  1. `#chains = n!` — the maximal chains are the orderings of `[n]`
     (`Permutations.perms_length`, the enumeration the repo previously lacked);
  2. `#chains through a size-k set A ≥ k!·(n−k)!` — the family
     `{σ ++ τ : σ ∈ perms(truePos A), τ ∈ perms(falsePos A)}` is duplicate-free
     (`perms_nodup` + append-injectivity), each member incident to `A`
     (`inc_concat`: its size-`k` prefix-set *is* `A`) and a genuine chain
     (`perms_append_mem` + `perms_respects`), counted `k!·(n−k)!` by
     `perms_length`.

Feeding these into `lym_double_count` gives `Σ_{A∈F} |A|!(n−|A|)! ≤ n!`, hence
(via `binom_mul_fact : C(n,k)·k!·(n−k)! = n!`) `|F| ≤ C(n,⌊n/2⌋)`.  Closing this
required completing `perms` to its full characterisation — `perms_length = n!`,
`mem_perms_iff` (exactly the permutations), and `perms_nodup` — reusable
infrastructure (the Leibniz determinant sums over the same `n!`).  The same
`perms`/subset toolkit leaves Erdős' named Ramsey bound a single edge-indexing
step (its subset count is `Sperner.layer_size`).

## Witnesses

  - `lean/E213/Lib/Math/Combinatorics/Sperner.lean` — `layer_size`,
    `eq_of_subseteq_card_eq`, `kLayer_isAntichain`, `lower_bound`, `absorb`,
    `binom_le_binom_mid`, `uniform_antichain_le`, `sumOver_swap`,
    `lym_double_count`, `binom_mul_fact`, `fact_mul_ge_mid`,
    `sperner_upper_bound`.  47/47 PURE.
  - `lean/E213/Lib/Math/Combinatorics/Permutations.lean` — `perms_length`
    (`= n!`), `mem_perms_iff`, `perms_nodup`, `perms_append_mem`.  21/21 PURE.
  - `lean/E213/Lib/Math/Combinatorics/SpernerChains.lean` — the chain model:
    `inc_concat`, `chain_cap` (`hcap`), `chain_low` (`hlow`), and ★★★
    `sperner` / `sperner_theorem` (the named bound, unconditional).  49/49 PURE.
  - the dual it mirrors: `Lib/Math/Combinatorics/{CountExistence,RamseyLowerBound}.lean`
    (the union bound) + `probabilistic_method.md`.
  - residue carrier: `Lib/Math/Combinatorics/BoolEnum.lean` (`allBoolLists`).
  - instruction set: `seed/PROOF_ISA.md`, `lean/E213/Lens/ProofISA.lean`.
