# Why the probabilistic method works — Erdős' `R(k,k) > 2^{k/2}`, compiled

**Reproduced result.** Erdős (1947): if `2·C(N,k) < 2^{C(k,2)}` then `K_N` has
a 2-colouring with no monochromatic `K_k`, so `R(k,k) > N`; in particular
`R(k,k) > 2^{k/2}`.  The founding theorem of the *probabilistic method*.

**Why we picked it.** Its proof move is *not* one of the eight named ISA
instructions (`seed/PROOF_ISA.md`).  Reproducing it tests whether the move
(a) reduces to the existing eight or (b) forces a new primitive — and the
answer, below, is (b): it surfaces **COUNT**, the quantitative `GAP` witness
the repo already used across ≈25 Lean files as `pigeonhole` without ever naming it an
instruction.

The surface move is one line:

> **`#bad < #total ⟹ a good object exists`.**

Everything interesting is in *why that line is a proof*.  Three layers, each a
∅-axiom witness built in `Lib/Math/Combinatorics/{CountExistence,RamseyLowerBound}.lean`.

## Layer 1 — why a deficit *forces* an object (and constructively)

The colouring space is not an abstract infinity to be searched by faith.  It is
a **finite residue**: `allBoolLists n` (`BoolEnum`) is the fold of `n` binary
distinguishings, the ∅-axiom stand-in for "all `2ⁿ` colourings", carried as a
`List` so equality is decidable and the count is `List.length` — no `Fintype`,
no `Classical`.

On a finite enumerated residue, *"not every element is bad"* is not an
existence-claim awaiting choice; it is **a search that terminates**:

```
deficit_exists : bcount bad L < L.length → ∃ l, l ∈ L ∧ bad l = false
```

(`CountExistence.deficit_exists`, ∅-axiom.)  Proof = walk `L`; the count
guarantees the walk meets a `false`.  *This is why the probabilistic method is
constructive at all:* the "probability" never leaves the finite residue — it is
normalised counting, and the witness is found, not posited.

## Layer 2 — why the per-event count is `2 · 2^{E−m}`

A "monochromatic on `S`" event constrains only the `m = C(k,2)` edges **inside**
`S`; the other `E − m` edges are untouched.  The count of colourings hit by the
event therefore **factors**, and the factorization is the whole content:

```
count_factor : bcount (fun l => p (l.drop r)) (allBoolLists (r + m))
                 = 2^r * bcount p (allBoolLists m)
```

(`RamseyLowerBound.count_factor`, ∅-axiom.)  A predicate blind to the `r` free
edges counts `2^r ·` its count on the constrained block.  **Why `2^r`:** each
free edge is one distinguishing, and *one distinguishing doubles the residue*
(`allBoolLists (n+1)` is two copies of `allBoolLists n` — prepend `false`,
prepend `true`).  Independent distinguishings **multiply**, so the count
separates into (free part) × (constrained part).

The constrained block is constant in exactly two ways:

```
bcount_const : bcount isConst (allBoolLists (m+1)) = 2
```

(`BoolEnum.bcount_const` — the two shared colours.)  Composing:

```
mono_event_count : bcount (fun l => isConst (l.drop r)) (allBoolLists (r+(m+1)))
                     = 2^(r+1)
```

(`RamseyLowerBound.mono_event_count`, ∅-axiom) — i.e. `2^r · 2 = 2·2^{E−m}`,
Erdős' per-event count, **derived**, the `2` and the `2^r` each named by the
fact that produces it.

## Layer 3 — why counting is a proof at all (the residue-level reason)

"How many" is not imported probability.  It is a **reading of the residue** —
the count-Lens — and by Layer 2 the residue's cardinality is built
*multiplicatively from its distinguishings*.  That single fact explains the
whole method at once:

  - **bad events factor** — locality (an event reads a sub-block) ⟹ a product
    (`count_factor`);
  - **the union bound holds one-directionally** — overlaps are double-counted,
    which is safe for an *upper* bound, because `GAP` only needs non-coverage,
    not exact size:
    `union_bound : bcount (anyBad preds) L ≤ totalCount preds L`
    (`CountExistence.union_bound`, ∅-axiom);
  - **deficit forces a found witness** — Layer 1.

Assembled, this is exactly the `GAP` instruction (`a reading does not cover its
codomain; the surplus is the residue`) — but with a **quantitative** witness:
where the catalogued `isa_gap` (`exists_non_lens_expressible`) supplies
non-coverage *qualitatively*, here non-coverage is `Σ|badᵢ| < |codomain|`, a
cardinality comparison:

```
count_existence : totalCount preds (allBoolLists n) < 2^n
                    → ∃ l, l ∈ allBoolLists n ∧ anyBad preds l = false
erdos_schema    : (∀ p ∈ preds, bcount p (allBoolLists n) ≤ c) → preds.length * c < 2^n
                    → ∃ l ∈ allBoolLists n, ∀ p ∈ preds, p l = false
```

(`CountExistence.{count_existence, erdos_schema}`, ∅-axiom.)

**The answer to "why".** Erdős did not reach outside the colouring space.  He
read the *same* finite residue's size two ways — total `2^E` versus the bad
sum — and when the total exceeds the bad, the surplus is forced.  The primitive
doing the work is **multiplicativity of counting in the residue's
distinguishings**; it is what makes events factor, the union bound safe, and
the deficit fatal — three consequences of one residue-level fact, not three
tricks.  Call that primitive **COUNT** (deficit ⟹ existence): the quantitative
`GAP` witness, structurally one `GAP`-arrow read by cardinality, of which
`pigeonhole` (`N+1 → N` non-injective) is the qualitative face the repo already
leaned on across ≈25 Lean files.

## Compiled form

```
R(k,k) > N
  = COUNT            (deficit ⟹ existence ; count_existence / erdos_schema)
  ∘ count-READ       (the residue's size, two ways ; bcount)
  ∘ DISTINGUISH      (the colouring space = a fold of edge-distinguishings)
```

## The named bound, closed

`erdos_schema` + the `K_N` edge model give the *named* `R(k,k) > N`
unconditionally (`RamseyNamedBound.ramsey_lower`, ∅-axiom):

  1. the per-event count is the `Option Bool` constraint count — permutation
     invariance is *not* needed.  Each `none` doubles, each `some` fixes
     (`matchesC_count : bcount (matchesC c) (allBoolLists c.length) = 2^countNone c`),
     so an arbitrary subset's "monochromatic" event
     `matchesC (all-some-false on S) ∨ matchesC (all-some-true on S)` has count
     `2·2^{E−C(k,2)}` — once the count of internal edges of `S` is `C(|S|,2)`
     (`pairsCount_eq`, the Pascal step `binom_succ_2`: each new vertex pairs with
     all earlier ones).
  2. the event list has length `C(N,k)` — the `k`-subsets, enumerated as
     `Sperner.kLayer N k` with `kLayer_card = C(N,k)` (the same subset count that
     reads a layer of the Boolean lattice in the Sperner compilation).

Feeding `t = C(N,k)`, `c = 2·2^{E−C(k,2)}`, `E = C(N,2)` into `erdos_schema`, its
hypothesis `t·c < 2^E` is `2·C(N,k) < 2^{C(k,2)}`, and the conclusion is a
2-colouring of `K_N` with no monochromatic `K_k` — `R(k,k) > N`.  Witness:
`lean/E213/Lib/Math/Combinatorics/RamseyNamedBound.lean`, 13/13 PURE.

## Witnesses

  - `lean/E213/Lib/Math/Combinatorics/CountExistence.lean` —
    `deficit_exists`, `union_bound`, `count_existence`, `erdos_schema`.
  - `lean/E213/Lib/Math/Combinatorics/RamseyLowerBound.lean` —
    `count_factor`, `mono_event_count`.
  - `lean/E213/Lib/Math/Combinatorics/BoolEnum.lean` — the residue carrier,
    `bcount_const`.
  - instruction set: `seed/PROOF_ISA.md`, `lean/E213/Lens/ProofISA.lean`.
