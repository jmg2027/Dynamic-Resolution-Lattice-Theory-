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
| `RamseyNamedBound.lean` | **R(k,k) > N named, CLOSED**: the K_N edge model — `pairsCount_eq` (#internal edges of S = C(|S|,2), via `binom_succ_2`), `monoEvent_count` (per-event ≤ `2·2^{C(N,2)−C(k,2)}`), ★★ `ramsey_lower` (instantiates `erdos_schema` with t=C(N,k)=`kLayer_card`) | ∅-axiom |
| `Permutations.lean` | permutation enumeration: `perms`, ★ `perms_length` (`= fact l.length`, the `n!` count), `mem_perms_iff` (`p ∈ perms l ↔ LPerm p l` — exactly the permutations, via `insert_comm`), `self_mem_perms`, `perms_append_mem` (orderings concatenate).  The chain-count infra for the named Sperner bound; reusable for the Leibniz determinant sum | ∅-axiom |
| `Sperner.lean` | Sperner's theorem compiled to **COUNT**'s double-counting face (LYM = dual union bound).  `layer_size` (layer = binomial, the READ), `eq_of_subseteq_card_eq` (SEPARATE), `lower_bound` (tight), `binom_le_binom_mid` (unimodality via `absorb`), `uniform_antichain_le` (single-layer Sperner, general), `lym_double_count`/`sumOver_swap` (the engine), `binom_mul_fact`/`fact_mul_ge_mid` (the arithmetic), ★ `sperner_upper_bound` (the abstract reduction: any chain model ⟹ `\|F\| ≤ C(n,⌊n/2⌋)`) | ∅-axiom |
| `SpernerChains.lean` | the geometric chain model discharging both `sperner_upper_bound` hypotheses (chains = `perms (idxList n)`, `inc` = prefix-set): `chain_cap` (`hcap`, nesting), `chain_low` (`hlow`, the `k!(n−k)!` injection via `perms_append_mem`/`inc_concat`), ★★★ `sperner` / `sperner_theorem` — **Sperner's theorem proven unconditionally** | ∅-axiom |
| `LymInequality.lean` | the **LYM / Bollobás–LYM inequality**, the per-term refinement Sperner discards: `lym_inequality` (engine form over any chain model), ★★ `lym_antichain` (named, unconditional: `Σ_{A∈F} \|A\|!(n−\|A\|)! ≤ n!` = `Σ 1/C(n,\|A\|) ≤ 1` cleared of denominators), `lym_tight_layer` (sharpness — a full layer saturates at `n!`; the layers are the extremal antichains), `sperner_via_lym` (LYM ⟹ Sperner via the `min` step + cancel).  Reuses `Sperner.lym_double_count` + `SpernerChains.{chains_length,chain_cap,chain_low}` | ∅-axiom |
| `BollobasSetPair.lean` | **Bollobás' set-pair inequality** `m ≤ C(a+b,a)` (the COUNT double-count on the *favour*-incidence pairs × orderings).  New heart: `before` + ★ `before_antisymm` (ordering antisymmetry, no `Nodup`), `favours`/`favours_before`, ★ `bollobas_cap` (cross-intersection ⟹ ≤ 1 favoured pair per ordering — the column cap, the content of Bollobás).  ★ `bollobas_sum` (the engine = `lym_double_count` on favours, unconditional), ★★ `bollobas` (named bound `\|F\| ≤ C(a+b,a)`, modulo the favour-count `V·(a+b)! = n!·a!·b!`).  Rung's arithmetic discharged: `favourCountTarget = C(n,a+b)·a!·b!·(n−a−b)!`, `favourCount_mul` (the identity), `bollobas_of_count` — `\|F\| ≤ C(a+b,a)` from the *single* geometric inequality `favourCountTarget ≤ #{favouring}` (the lone remaining rung, the `chain_low` analogue).  Reuses `lym_double_count`, `binom_mul_fact`, `SpernerChains.{truePos,idxList,perms,lcount_le_one_of}` | ∅-axiom |
| `ChainAntichain.lean` | **Mirsky + Dilworth on `2^[n]` (chain/antichain duality), both FULLY CLOSED**.  *Mirsky*: `chain_card_inj` (the *chain* SEPARATE), `IsChain`, ★ `chain_length_le` (height ≤ `n+1`), `initSeg`/`canonChain` + ★ `canonChain_max` (height achieved), `chain_layer_cap`, `mem_own_layer`, ★★ `mirsky_boolean` — longest chain `= n+1 =` #layers `=` min antichain partition.  *Dilworth*: `memBL`/`findChain` + ★★ `dilworth_lower` (any chain cover ≥ `C(n,⌊n/2⌋)`); the de Bruijn–Tengbergen–Kruyswijk SCD `scd`/`extendC`/`raiseC`, `scd_isChain` + ★★ `scd_chain_cover` (chain + cover), `scd_nonempty`; the **symmetric-level invariant** `consec`/`extendC_sym`/`raiseC_sym` + length helpers + ★★ `scd_sym` (`cardB` run `[k,…,n−k]`, `2k+|C|=n+1`), `sym_span`/`mem_consec` + `scd_has_middle`/`scd_middle_unique` (each chain meets `⌊n/2⌋` once); the **SCD partition** `mem_extendC`/`mem_raiseC`/`child_tail_mem` + `extendC_raiseC_disjoint` + ★★ `scd_same`/`scd_disjoint`/`scd_nodup` (chains disjoint, distinct; `scd_chain_nodup` via `consec_nodup`+`nodup_of_nodup_map`); the **count** `scd_vec_length`/`nodup_filter`/`filter_len_one`/`midFlat_{length,nodup,sub}` + ★★★ `scd_card` (`\|scd n\| = C(n,⌊n/2⌋)`) and ★★★ `dilworth_boolean` — **min chain cover `= C(n,⌊n/2⌋) =` max antichain** (Sperner).  ★★ `sperner_via_scd` — **Sperner from the partition** (antichain ↪ chains; the classical symmetric-chain proof, a third route after the LYM double count).  `mem_idxList_of_lt`. | ∅-axiom |
| `BollobasCount.lean` | **the favour-count injection — CLOSES Bollobás unconditionally** (36/36 PURE): `weave` (mask-guided interleave) + `weave_perm`, order preservation (`before_append_mem`/`weave_preserves_before`/`weave_favours`), the position partition (`restPos`/`disjointVec`, `partition_perm` + disjointness), `weave` recovery (`map_q_weave`/`filter_q_weave`/`filter_nq_weave`), `wovenFam` + `wovenFam_length` (`= favourCountTarget`)/`wovenFam_nodup`/`wovenFam_subset`, ★★ `favourCount_lower` (discharges the rung), ★★★ `bollobas_uniform` — `\|F\| ≤ C(a+b,a)`, `n`-independent, **unconditional ∅-axiom** | ∅-axiom |
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
is the *union bound* (`CountExistence` + `RamseyLowerBound` + `RamseyNamedBound`);
**Sperner**'s upper bound is its *dual*, the double count / LYM (`Sperner.lean`
engine + `SpernerChains.lean` chain model).  **Both named bounds are now closed
∅-axiom** — `RamseyNamedBound.ramsey_lower` (`R(k,k) > N`) and
`SpernerChains.sperner_theorem` — completing the proof-ISA COUNT series.  The
subset count `C(N,k)` is shared (`Sperner.layer_size` / `kLayer_card`).

## Out of scope (separate continuation)

  * Generic-degree generating function inverse (cup-Ring inverse,
    same as `CutLog` continuation).
  * Pell ArithFSM hierarchy expansion (already in DyadicFSM/).
