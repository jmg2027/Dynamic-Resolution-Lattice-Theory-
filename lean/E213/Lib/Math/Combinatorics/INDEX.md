# Combinatorics 213 — Module Index

Blueprint: `blueprints/math/10_combinatorics_213.md` (retired).

## Modules

| File | Topic | Status |
|---|---|---|
| `Binomial.lean` | Pascal table, symmetry, row sums, vanishing for k > n | ∅-axiom |
| `Catalan.lean` | C₀..C₇ table + recursion checks at n=3, 4 | ∅-axiom |
| `Stirling.lean` | S(n, k) recursion + Bell decomposition | ∅-axiom |
| `GeneratingFunction.lean` | formal power series, convolution, catalanGF | ∅-axiom |
| `Simplex5.lean` | (3,2) partition + S_3×S_2-invariant weight on Fin 5×Fin 5 | ∅-axiom |
| `Pigeonhole.lean` | no injection `Fin (N+1) → Fin N` (∅-axiom, core-lemma route avoided) | ∅-axiom |
| `Logic.lean` | umbrella for the `Logic/` sub-tree | — |
| `GraphConnectivity.lean` | abstract graph reachability (`Reach` inductive) → δ⁰-closed colouring is constant on a connected graph (`closed_const`, `closed_false_or_true`, b₀ = 1); instantiated for complete bipartite in `Cohomology/Bipartite/Parametric/KernelConstancyUniversal` | ∅-axiom |
| `Capstone.lean` | 4 cluster witnesses + total_witness | ∅-axiom |
| `Combinatorics.lean` | umbrella (sibling) | — |

## Key 213-native results

  * **Binomial = atomic finite**: `binom 5 6 = 0` (Grade-overflow,
    matches the cohomology truncation in `CutExpFiniteTruncation`).
    Pascal's row sums are decide-stable.
  * **Catalan numbers** counted directly: C₀..C₇ = (1, 1, 2, 5,
    14, 42, 132, 429).  Recursion verified at n=3, 4.
  * **Bell numbers** decompose into Stirling-of-second-kind.
  * **Generating functions = finite polynomials** modulo grade
    nilpotency.  No convergence questions — same paradigm reframe
    as `cutExp` (Probability marathon).

## Connection to existing infrastructure

  * `Lib/Physics/Simplex/Counts.lean`: `binom` definition + dim
    table.
  * `Lib/Math/NumberTheory/DyadicFSM/Pell/`: Pell hierarchy (already realized).
  * `Lib/Math/NumberTheory/DyadicFSM/Fib/`, `Trib/`: Fibonacci, Tribonacci.
  * `Lib/Math/Cohomology/Bipartite/`: K_{3,2} structure.
  * `Lib/Physics/AtomicBase/Pairs.lean`: 10-pair partition (3+1+6).
  * `Lib/Math/Cohomology/CutExpFiniteTruncation.lean`: paradigm
    parallel — generating functions are *finite polynomials*
    on the substrate, exactly like `cutExp` is a *finite Taylor
    sum*.

## Out of scope (separate continuation)

  * Ramsey's theorem (would benefit from cohomology bipartite).
  * Generic-degree generating function inverse (cup-Ring inverse,
    same as `CutLog` continuation).
  * Probabilistic method (would link to Probability 213 +
    Information 213 entropy).
  * Pell ArithFSM hierarchy expansion (already in DyadicFSM/).
