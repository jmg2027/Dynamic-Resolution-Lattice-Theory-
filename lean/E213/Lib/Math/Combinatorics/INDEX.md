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
| `BoolEnum.lean` | finite Bool-cardinality enumeration: `allBoolLists n` (all `2^n` length-`n` Bool lists) + `length = 2^n` + completeness + nodup; (generic `List` mem/nodup/filter/cardinality toolkit now lives in `Meta/Tactic/List213`).  Counting: `bcount` toolkit + `bcount_const` (= 2 constant colourings per nonempty length, the division-free universal count-Lens form of `b₀ = 1`); `bcount_headFalse` (= `2^(V−1)`, canonical coboundary reps) + complement involution / head-`false` transversal | ∅-axiom |
| `Capstone.lean` | 4 cluster witnesses + total_witness | ∅-axiom |
| `CountExistence.lean` | **COUNT** = quantitative `GAP`: `union_bound`, `deficit_exists` (deficit ⟹ ∃ good, finite search), `count_existence`, `erdos_schema` (the probabilistic method as one theorem) | ∅-axiom |
| `RamseyLowerBound.lean` | the per-event count's *why*: `count_factor` (free bits double), `mono_event_count` (`2·2^{E−m}`), `matchesC_count` (arbitrary-subset count) | ∅-axiom |
| `Sperner.lean` | Sperner's theorem compiled to **COUNT**'s double-counting face (LYM = dual union bound).  `layer_size` (layer = binomial, the READ), `eq_of_subseteq_card_eq` (SEPARATE), `lower_bound` (tight), `binom_le_binom_mid` (unimodality via `absorb`), `uniform_antichain_le` (single-layer Sperner, general), `lym_double_count`/`sumOver_swap` (the engine).  Named bound's chain-count = honest rung | ∅-axiom |
| `LinearDependence.lean` | `dimension_bound_is_count` — `m>n` vectors in `𝔽₂^n` dependent via subset-sum collision (= COUNT in a linear codomain); `vsum`/`vxor` | ∅-axiom |
| `ParityInvariant.lean` | mutilated chessboard: `tiling_balanced` (conserved colour-count = READ ∘ SEPARATE), `corners_same_colour`; `par` = `Mod213.parity` | ∅-axiom |
| `KonigConditional.lean` | König boundary: `konig_conditional`/`walk` (the LOOP, internal); `InfBelow`/`InfChildExists` (the un-dischargeable `DECIDE` = the exterior) | ∅-axiom (conditional) |
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

## proof-ISA reproductions (`theory/essays/proof_isa/`)

The probabilistic method, the linear-algebra / dimension method, the parity /
invariant method, Sperner's theorem, and König's lemma are compiled down the
proof-ISA here — the "why" of each lives in `theory/essays/proof_isa/`.  Two of
them sit on `COUNT`'s two faces: the Ramsey **lower** bound `R(k,k) > 2^{k/2}`
is the *union bound* (`CountExistence` + `RamseyLowerBound`); **Sperner**'s upper
bound is its *dual*, the double count / LYM (`Sperner.lean`).  Each has its
engine built ∅-axiom with the *named* closure a permutation-count bookkeeping
rung (Ramsey: `t = C(N,k)`; Sperner: `n!` and `k!(n−k)!`) —
`research-notes/frontiers/`.

## Out of scope (separate continuation)

  * Generic-degree generating function inverse (cup-Ring inverse,
    same as `CutLog` continuation).
  * Pell ArithFSM hierarchy expansion (already in DyadicFSM/).
