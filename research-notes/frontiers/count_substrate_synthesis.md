# Synthesis — the COUNT substrate, after both named bounds closed

**Anchor.** Closing both named COUNT bounds — Sperner (`SpernerChains.sperner_theorem`)
and Erdős' `R(k,k) > N` (`RamseyNamedBound.ramsey_lower`) — built two reusable
substrates (the `perms` enumeration; the subset count `kLayer_card = C(N,k)`) and
exposed patterns worth harvesting.

## Patterns

- **Dual COUNT faces, one residue.**  The union bound (Ramsey, *deficit ⟹
  existence*) and the double count (Sperner, *per-column cap ⟹ row-sum bound*)
  are one `0/1` incidence matrix read by rows vs columns (`Sperner.sumOver_swap`
  = Fubini), and both consume the *same* subset count `C(N,k)`
  (`Sperner.layer_size` reads a Boolean-lattice layer; `RamseyNamedBound` reads
  the monochromatic-event list).  One Raw (the finite subset residue), two Lens
  readouts — the count-Lens essay's thesis, now load-bearing in two theorems.

- **"Engine + honest rung" closes once the enumeration infra exists.**  Both
  named bounds sat as "honest rungs" over built abstract engines (`erdos_schema`,
  `lym_double_count`) until the *enumeration* was built: `perms` (orderings, `n!`)
  for Sperner's chains, the `kLayer`/edge model for Ramsey.  The reusable lift:
  an abstract existence/counting engine's *named* instantiation is a
  finite-enumeration bridge, and the enumeration (`perms_length`/`layer_size`) is
  shared infrastructure, not per-problem.

- **`nodup`-of-`flatMap`-of-disjoint-fibres** is a recurring counting-injection
  idiom — `Permutations.perms_nodup` (insert-families disjoint via `eraseFirst`)
  and `SpernerChains.chain_low` (the `{σ++τ}` family nodup via append-injectivity)
  are the same shape: `nodup_flatMap213` over a nodup base with disjoint nodup
  fibres, then `nodup_length_le_of_subset` for the count bound.

- **The propext/Classical tax on core arithmetic recurs.**  Closing these needed
  clean replacements for core lemmas that carry `propext` — and one
  (`Nat.mul_lt_mul_right`) carries **`Classical.choice`**.  Swapped for
  `Binomial.add_mul_pure`, `NatHelper.{mul_assoc,mul_left_comm,add_sub_*}`,
  `List213.length_map`, and ad-hoc privates (`mul_lt_mul_right_clean`,
  `pow_add_clean`, `succ_sub_clean`).

## New questions

- ✓ **A clean strict-order + pow Meta suite — CLOSED.**  The canonical
  propext-free forms are now all in `Meta/Nat`: `mul_lt_mul_right` =
  `NatRing213.nat_mul_lt_mul_right` (also `_left` + `mul_lt_mul_left_pure`),
  `pow_add` = `PureNat.pow_add` (general base), `succ_sub` =
  ★ `NatRing213.nat_succ_sub` (new — `(n+1)−m = (n−m)+1` for `m ≤ n`), and
  strict-mono = the `nat_mul_lt_mul_*` pair.  The scattered private
  `SpernerChains.succ_sub_clean` is dropped in favour of `nat_succ_sub`.  Core
  `Nat.mul_lt_mul_right` carries `propext`+`Classical.choice`+`Quot.sound`;
  `Nat.pow_add`/`Nat.succ_sub` carry `propext` — all displaced.

- **More COUNT-family named bounds on the same substrate.**  ✓ **The explicit
  LYM inequality `Σ_{A∈F} 1/C(n,|A|) ≤ 1` is now closed** —
  `LymInequality.lym_antichain` (division-free form `Σ |A|!(n−|A|)! ≤ n!`),
  with `lym_tight_layer` (sharpness) and `sperner_via_lym` (LYM ⟹ Sperner); it
  was the existing `lym_double_count` engine stopped one line before Sperner's
  `min`-collapse.

  ✓ **Bollobás' set-pair inequality `m ≤ C(a+b,a)` — the heart is closed** —
  `BollobasSetPair` (18/18 PURE).  The new content (the column cap: cross-
  intersection + per-pair disjointness ⟹ each ordering favours ≤ 1 pair, via
  `before_antisymm`) and the engine (`bollobas_sum` = `lym_double_count` on the
  favour-incidence) are done; the named bound `bollobas` holds **modulo the
  favour-count rung** `V·(a+b)! = n!·a!·b!`.

  **Open rung — the favour-count injection.**  Arithmetic now **discharged**
  (`favourCount_mul`, `bollobas_of_count`): `favourCountTarget = C(n,a+b)·a!·b!·
  (n−a−b)!` satisfies `·(a+b)! = n!·a!·b!`, so the rung collapses to the *single*
  geometric inequality `favourCountTarget ≤ #{orderings favouring (A,B)}`.  The
  injection (ordering-count analogue of `SpernerChains.chain_low`): a favouring
  ordering is `weave mask (σ_A ++ σ_B) σ_R` — interleave an ordering of `A` then
  `B` into the `mask`-true slots (`mask ∈ kLayer n (a+b)`, `C(n,a+b)` of them),
  the rest `R` into the false slots.

  ✓✓ **Bollobás is fully CLOSED** — `BollobasCount` (36/36 PURE).  Enumeration
  done: the position partition (`partition_perm`, `restPos`/`disjointVec` +
  disjointness lemmas), the `weave` filter/map recovery (`map_q_weave`/
  `filter_q_weave`/`filter_nq_weave`), `wovenFam` with its length
  (`wovenFam_length = favourCountTarget`), nodup (4-level via recovery) and
  subset (`wovenFam_subset` — every woven ordering is a favouring permutation).
  `favourCount_lower` discharges the rung; ★★★ `bollobas_uniform` —
  `|F| ≤ C(a+b,a)`, `n`-independent, **unconditional ∅-axiom**.

  ✓✓ **Mirsky on `2^[n]` is CLOSED** — `ChainAntichain` (15/15 PURE): the dual of
  Sperner.  `chain_card_inj` (chain SEPARATE), `chain_length_le` (height ≤ `n+1`),
  `canonChain_max` (height achieved — the `∅⊂…⊂[n]` chain has exactly `n+1`),
  and ★★ `mirsky_boolean` — longest chain = `n+1` = #layers (the size-layers are
  the minimum antichain partition).

  ✓✓✓ **Dilworth on `2^[n]` is FULLY CLOSED** (`ChainAntichain`, ∅-axiom).
  Narrative promoted to `theory/essays/proof_isa/chain_antichain_duality.md`.
  ★★★ `dilworth_boolean`: `scd n` is a chain cover of *exactly* `C(n,⌊n/2⌋)`
  chains (`scd_card`) and every chain cover needs `≥ C(n,⌊n/2⌋)` (`dilworth_lower`)
  — so **min chain cover `= C(n,⌊n/2⌋)` = max antichain** (Sperner), the chain-cover
  dual of Mirsky.  ✓ `dilworth_lower`: any chain cover ≥ `C(n,⌊n/2⌋)` (via
  `memBL`/`findChain` — choice-free injective assignment).  ★★★ `scd_card`:
  `|scd n| = C(n,⌊n/2⌋)` via the middle-layer trace
  `flatMap (C ↦ C.filter (cardB=⌊n/2⌋))` — length `= |scd n|` (one per chain,
  `filter_len_one` + `length_flatMap213_const`), nodup (the SCD partition), set-equal
  to `kLayer n ⌊n/2⌋` (cover + length-`n`) ⟹ equal length.

  **The SCD partition (the crux, CLOSED).**  ★★ `scd_same` (a vector shared by two
  chains forces them equal — induction: shared tail in both parents, parents equal by
  IH; within a parent `extendC`/`raiseC` disjoint via `extendC_raiseC_disjoint`),
  `scd_disjoint` (the `≠` form), ★★ `scd_nodup` (no repeated chain — distinct parents
  yield disjoint children via `scd_same`, `extendC_ne_raiseC` within a parent).  Infra:
  `mem_extendC`/`mem_raiseC`/`child_tail_mem` (tail-membership), `scd_chain_nodup`
  (each chain nodup, from `consec_nodup` + `nodup_of_nodup_map`), `scd_vec_length`
  (chain vectors have length `n`), `nodup_filter` (propext-free).
  No `extendC`/`raiseC` injectivity was needed — collisions are killed by IH
  disjointness.

  **[historical — the SCD construction]** (a `C(n,⌊n/2⌋)`-chain cover,
  de Bruijn–Tengbergen–Kruyswijk).  Construction (new bit at the *front*,
  chains bottom-to-top):
  - `extendC [v₀,…,v_L] = [false::v₀,…,false::v_L, true::v_L]` (length `L+2`);
    `raiseC [v₀,…,v_L] = [true::v₀,…,true::v_{L−1}]` (length `L`, empty if `L=0`).
  - `scd 0 = [[[]]]`; `scd (n+1) = (scd n).flatMap (fun C => extendC C :: (if
    raiseC C = [] then [] else [raiseC C]))`.
  Proof obligations: (a) **chain** — ✓✓ **CLOSED** (`ChainAntichain` §6):
  `extendC`/`raiseC`/`scdStep`/`scd` (construction via `flatMap213`),
  `extendC_sorted`/`raiseC_sorted` (constructors preserve `subseteqB`-`Pairwise`,
  via `extendC_head`/`raiseC_head` + `subseteqB_cons_same`/`subseteqB_false_true`),
  `scd_sorted`, and ★★ `scd_isChain` — every member of `scd n` is a chain.
  (b) **cover** — ✓✓ **CLOSED** (`ChainAntichain` §7): `false_mem_extendC`,
  `true_mem`, `extendC_mem_scdStep`/`raiseC_mem_scdStep`, ★★ `scd_cover` (every
  length-`n` vector in some `scd n` chain) and `scd_chain_cover`.
  (c) **count** `= C(n,⌊n/2⌋)` — *the last rung*.  ✓✓ **symmetric-level invariant
  CLOSED** (`ChainAntichain` §9–11): `consec k m` (the run `[k,…,k+m−1]`),
  `extendC_sym`/`raiseC_sym` (run shifts), length helpers
  (`consec_length`/`extendC_length`/`raiseC_length`), the `raiseC` span arithmetic
  (`raise_sum_arith`), and ★★ `scd_sym` — every chain of `scd n` satisfies
  `SymChain n C := ∃ k, C.map cardB = consec k |C| ∧ 2k+|C| = n+1`.  ✓✓ **straddle
  CLOSED**: `sym_span` (`k ≤ ⌊n/2⌋` and `k+⌊n/2⌋ ≤ n` from `2k+|C|=n+1`),
  `mem_consec`, ★ `scd_has_middle` (every chain has a `⌊n/2⌋`-element) + ★
  `scd_middle_unique` (exactly one, via `chain_card_inj`).  ✓✓ **lower bound
  realised**: `scd_lower` — `scd n` is a chain cover so `C(n,⌊n/2⌋) ≤ |scd n|`
  (`dilworth_lower`).
  `scd_card` realised route (A)'s structure positively: the middle-layer trace is
  nodup *because* the chains partition (`scd_disjoint`), and the count drops out of
  `length_flatMap213_const` (constant fiber length 1) — no separate length-doubling
  or `same-set-same-length` lemma was needed.

  **Mirsky + Dilworth together** now give the full chain/antichain duality on the
  Boolean lattice ∅-axiom: longest chain `= n+1 =` min antichain partition
  (`mirsky_boolean`), and min chain cover `= C(n,⌊n/2⌋) =` max antichain
  (`dilworth_boolean`).  This closes the COUNT-substrate extremal-combinatorics
  frontier (LYM, Bollobás, Sperner, Mirsky, Dilworth all ∅-axiom).

  **Sperner now has three ∅-axiom proofs** on this substrate: the LYM double count
  (`SpernerChains.sperner`), `sperner_via_lym` (the named inequality + the `min`
  step), and ★★ `sperner_via_scd` (Dilworth's partition ⟹ Sperner — an antichain
  meets each symmetric chain ≤ once, so injects into `scd n`).  One residue, the
  same COUNT face read three ways.

  **The SCD partition is fully characterised**: ★★ `scd_card` (`C(n,⌊n/2⌋)` chains)
  + ★★ `scd_flat_length` (the flattened chains list every subset once — total `2^n`,
  via `scd_flat_nodup` + cover + length-`n` ⟹ set-equal to `allBoolLists n`).  So the
  symmetric chains partition `2^[n]` into `C(n,⌊n/2⌋)` chains holding all `2^n` subsets.

- ✓✓✓ **Leibniz determinant over `perms` — FULLY CLOSED.**  `Linalg213` carries
  the complete determinant from scratch, ∅-axiom: `Permutation.leibDet n M =
  Σ_{σ ∈ perms n} sign(σ)·Πᵢ M i (σ i)`, with `PermClosure` (enumeration
  sound/complete/nodup, ★ `perms_swap_closed`, ★ `leibDet_rowSwap` alternating,
  equal-rows ⟹ 0, multilinearity, degeneracy corollaries) and `Laplace`
  (cofactor expansion ★ `cofactor_row0`/`cofactor_row_i`, ★ `leibDet_eq_det`
  bridge to the recursive `DetN.det`, adjugate `M·adj M = det·I`).
  ★★ **The bridge between the two permutation developments is now explicit**
  (`PermBridge`): `permsOf xs = Combinatorics.Permutations.perms xs` (same list,
  flatMap213 vs core flatMap), transporting the count `perms_length = fact` to
  the determinant — `perms_card : (perms n).length = fact n` and
  `leibDet_card` (**the determinant is a sum of exactly `n!` signed diagonal
  products**).  Downstream: `CayleyHamilton` (integer `χ_M(M)=0`) +
  `CharPolyAdj` (polynomial adjugate over `ℤ[X]`).

## Cross-references

`theory/essays/proof_isa/{counting_as_cardinality,sperner_double_counting,probabilistic_method}.md`;
`lean/E213/Lib/Math/Combinatorics/{Sperner,SpernerChains,Permutations,RamseyNamedBound,CountExistence,RamseyLowerBound}.lean`;
`lean/E213/Lib/Math/Algebra/Linalg213/Permutation.lean`; `seed/PROOF_ISA.md`.
