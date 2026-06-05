# G205 — compiling Sperner's theorem: COUNT's double-counting face + the chain-count rung

**Tier 1 (volatile), research memo.**  Continues the proof-ISA compilation
series (G200): take a *solved* hard result and compile it down the instruction
set (`seed/PROOF_ISA.md`), mapping where the eight named instructions reach.

Target: **Sperner (1928)** — the largest antichain in the Boolean lattice
`2^[n]` has size `C(n,⌊n/2⌋)`.  Picked as the **dual** of the probabilistic
method (G200): G200 compiled to `COUNT` via the *union bound* (deficit ⟹
existence); Sperner's upper bound is the LYM inequality, the *double count*.
Question: is the dual a new instruction, or the same `COUNT` from the other
side?

## Verdict — same `COUNT`, mirrored (no new instruction)

The union bound and LYM are **one 0/1 incidence matrix** (subsets × maximal
chains) summed two ways:

  - **union bound** (G200): the matrix (bad-event × point) summed to over-count
    coverage ⟹ an upper bound on the bad set ⟹ a good point left over.
  - **LYM** (here): each *column* (chain) hits the antichain ≤ once, so the
    *row* sum (Σ chains-through-`A`) ≤ #chains.

`sumOver_swap` (Fubini) is the matrix's two readings; `lym_double_count` is the
column-cap ⟹ row-bound. So Sperner sits on `COUNT`'s **double-counting** face —
`pigeonhole`/union-bound = *deficit ⟹ existence*, LYM = *per-column cap ⟹
row-sum bound* — the same `GAP`-by-cardinality.

The Sperner **number** is a *separate* composition (not the upper bound):
READ (`layer_size`: layer = `binom n k`, count recursion = Pascal) ∘
unimodality (`binom_le_binom_mid`, engine = the absorption identity `absorb`).
The extremal antichain is a SEPARATE (`eq_of_subseteq_card_eq`: equal-size
distinct sets incomparable).

## What is closed (general, ∅-axiom) — `Lib/Math/Combinatorics/Sperner.lean`

`layer_size`, `eq_of_subseteq_card_eq`, `lower_bound` (tight existence),
`binom_le_binom_mid` (unimodality), `uniform_antichain_le` (single-layer
Sperner — fully general), `sumOver_swap` + `lym_double_count` (the engine), plus
the arithmetic + reduction below.  47/47 PURE.

## Open rung (bookkeeping, no new "why") — the permutation chain-counts

The engine `lym_double_count` is general; the *named* general upper bound needs
the chain model's two arithmetic counts:

  1. `#maximal chains = n!` (orderings of `[n]`);
  2. `#chains through a size-`k`-set = k!·(n−k)!`.

Then `Σ_{A∈F} |A|!(n−|A|)! ≤ n!`, and via `binom_mul_fact : binom n k · k!·(n−k)! = n!` the LYM fractional form `Σ 1/C(n,|A|) ≤ 1`,
hence `|F| ≤ C(n,⌊n/2⌋)`.

**STATUS — CLOSED ∅-axiom (named bound fully proven).**  The whole compilation
is built: the full `perms` characterisation (`perms_length = n!`, `mem_perms_iff`,
`perms_nodup`, `perms_append_mem` — `Permutations.lean`, 21/21 PURE), the arithmetic
(`binom_mul_fact`, `fact_mul_ge_mid` — `Sperner.lean`, 47/47 PURE), and the geometric
chain model (`SpernerChains.lean`, 49/49 PURE): `inc` = prefix-set, `chain_cap`
(`hcap`), `chain_low` (`hlow`, the `k!(n−k)!` injection), and ★★★ `sperner` /
`sperner_theorem` — Sperner's theorem (1928) proven unconditionally, the largest
antichain of `2^[n]` has size exactly `C(n,⌊n/2⌋)`.  Promoted:
`theory/essays/proof_isa/sperner_double_counting.md`.

For Ramsey's named bound the subset-count side is *already* in hand:
`Sperner.layer_size` counts the `k`-subsets (`= C(n,k)`); what remains there is
the `K_N` edge↔position indexing into `erdos_schema`.

Essay (the "why", promoted): `theory/essays/proof_isa/sperner_double_counting.md`.
