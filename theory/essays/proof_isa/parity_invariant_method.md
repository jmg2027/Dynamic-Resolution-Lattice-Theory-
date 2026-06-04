# Why the parity / invariant argument works — it is READ ∘ SEPARATE

**Reproduced result.** The mutilated chessboard: an `8×8` board minus two
opposite corners cannot be tiled by dominoes (and the general invariant method
behind it — the 15-puzzle's unsolvable half, mod-`n` colouring obstructions,
conservation laws).

**Why we picked it.** A "preserved quantity obstructs reachability" move looks
like it could be a *new* instruction (CONSERVE), or — since parity is `count`
mod 2 — collapse to **COUNT** a third time.  Reproducing it answers which.

## The argument

Colour each cell by the parity of `i + j`.  A domino covers two **adjacent**
cells; adjacency steps one coordinate by `1`, flipping the parity — so a domino
covers **one cell of each colour**.  Hence any tiling covers the two colours
**equally**.  The mutilated board's two removed corners share a colour, so its
colour-counts are unequal — no tiling can cover it.

## The "why" — neither COUNT nor a new instruction

It is **not COUNT.**  COUNT is *deficit ⟹ existence* (`Σ|badᵢ| < |total|` forces
a good object).  Here nothing is forced to exist; a conserved quantity is shown
to **differ**, obstructing.  Opposite direction.

It is **not a new instruction.**  Two pieces, both already named:

  - **the conservation is READ being a fold.**  The colour-count is a
    catamorphism over the cell list (`ctrue`/`cfalse`), i.e. a **READ**.  A READ
    is *by definition* a homomorphism over the structure it folds, so it is
    automatically additive over a tiling: "each domino reads one of each ⟹ the
    whole reads them equal" is not a new law, it is READ being a fold.  The
    ∅-axiom witness:

    ```
    tiling_balanced
      : (∀ d ∈ t, Adj d.1 d.2) → ctrue (cover t) = cfalse (cover t)
    ```

    (`Lib/Math/Combinatorics/ParityInvariant.lean`, PURE.)  The induction adds
    each domino's `(1,0)+(0,1)` contribution; the conserved equality is the
    fold's invariant.

  - **the obstruction is SEPARATE.**  Two states with different conserved value
    cannot coincide — a reading tells them apart.  `corners_same_colour`
    (PURE) seeds it: the removed corners share a colour, unbalancing the counts
    that every tiling keeps balanced.

So the parity method compiles to **READ ∘ SEPARATE**: a *conserved* reading
(`READ` as a fold) used to **SEPARATE** the reachable from the unreachable.

The local flip — adjacency reverses colour — is the only arithmetic, and in
213 it is **definitional**: parity is the `mod`-free `Bool` recursion
`parNat (n+1) = !(parNat n)`, so `adj_par` (adjacent ⟹ opposite colour) closes
by `rfl`.  (`Int`/`Nat.mod` would have imported `propext`/`Quot.sound`; the
`Bool` residue keeps it strict ∅-axiom.)

## Compiled form

```
mutilated board not tileable
  = SEPARATE          (corners share colour ⟹ counts unequal ⟹ ≠ any tiling)
  ∘ READ-as-fold      (colour-count conserved across the tiling ; tiling_balanced)
  ∘ DISTINGUISH       (the colour = the mod-free parity Bool of the cell)
```

## Where this lands among the reproductions

Three solved methods compiled so far, and the instruction set is holding:

| method | compiles to |
|---|---|
| probabilistic (Erdős) | **COUNT** (GAP-quantitative, colouring Lens) |
| linear-algebra / dimension | **COUNT** (GAP-quantitative, subset-sum Lens) |
| parity / invariant | **READ ∘ SEPARATE** (conserved fold separates) |

No new instruction has been forced.  Parity *could* have been "COUNT mod 2", but
its working direction is conservation→separation, so it lands on READ ∘ SEPARATE
instead — the GAP-side and the SEPARATE-side of the same eight, reached by
different famous techniques.  That the surface-diverse methods keep collapsing
onto the named eight is itself the cumulative evidence for the ISA's
completeness.

## Open rung (bookkeeping, no new "why")

`tiling_balanced` + `corners_same_colour` are the engine and the seed.  The
fully-named statement ("no domino tiling covers exactly the 62-cell mutilated
board") needs the board model: the full board's two colour-counts are equal
(`32 = 32`), removing two same-colour corners makes them `30 ≠ 32`, and a cover
equal to the board (as a multiset) would force `ctrue = cfalse`.  Finite
counting + a permutation-invariance of the count — no new "why".

## Connections to the corpus (sweep)

Cross-referencing against the existing PURE corpus (the same discipline that
sharpened the König boundary) located two anchors, one a reuse and one a kin:

  - **`par` reuses `Mod213.parity`** — the colour is the canonical ∅-axiom
    parity primitive (`E213.Tactic.Mod213.parity`, the smallest
    cohomological-trajectory primitive), not a local copy; the flip `adj_par` is
    `Mod213.parity_succ`.
  - **the conserved-fold pattern is the repo's δ⁰-colouring machinery** —
    `GraphConnectivity.IsClosed (Adj) (σ) := ∀ u v, Adj u v → σ u = σ v` with
    `closed_const`/`closed_false_or_true` (a colouring constant along a relation
    is globally one of two constants) is the *same shape* as a conserved
    reading along a dynamics, and the cohomology `KernelConstancyUniversal`
    promotes it (kernel `δ⁰` = the two constants, for connected `K_{NS,NT}^{(c)}`).
    The domino colouring is the **complementary** case — *opposite* on each
    adjacency (a proper 2-colouring / bipartite class function, `δ⁰par = `
    all-ones), not *same* on each edge (the kernel) — so it is the bipartite
    dual of the closed-colouring kernel, not a literal `IsClosed` instance.  The
    shared primitive is "a `READ` conserved along a relation"; the two readings
    sit on the two sides of `δ⁰`.

This is the same lesson as König: the conserved-reading move was already in the
corpus (δ⁰-closed colourings); the parity argument is one reading of it.

## Witnesses

  - `lean/E213/Lib/Math/Combinatorics/ParityInvariant.lean` —
    `par` (= `Mod213.parity`), `adj_par` (= `parity_succ`), `tiling_balanced`,
    `corners_same_colour`.
  - the conserved-fold corpus: `Lib/Math/Combinatorics/GraphConnectivity.lean`
    (`IsClosed`, `closed_const`), `Cohomology/.../KernelConstancyUniversal.lean`.
  - instruction set: `seed/PROOF_ISA.md`, `lean/E213/Lens/ProofISA.lean`
    (`isa_read`, `isa_separate`).
