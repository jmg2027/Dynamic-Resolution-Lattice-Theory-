# Chain/antichain duality — Mirsky and Dilworth as the dual of Sperner

**Reproduced result.** The two duality theorems for the Boolean lattice `2^[n]`,
both ∅-axiom:

  - **Mirsky** — the longest chain has `n + 1` members, and that number equals
    the minimum number of antichains needed to cover `2^[n]`
    (`ChainAntichain.mirsky_boolean`).
  - **Dilworth** — the minimum number of *chains* needed to cover `2^[n]` is
    `C(n, ⌊n/2⌋)`, and that equals the maximum antichain — Sperner's number
    (`ChainAntichain.dilworth_boolean`).

Sperner and LYM (`sperner_double_counting.md`, `lym_inequality.md`) bounded
**antichains** by counting chains. Mirsky and Dilworth are the **dual**: they
read the same lattice through *chains*, and the bounds turn into *partitions*.

**Why we picked it.** The proof-ISA thesis is that a theorem is compiled from a
shared instruction set, not cracked by problem-specific genius. Sperner's
compilation used two instructions — **SEPARATE** (an antichain has no two
comparable members) and **COUNT** (the chain/member double count). The natural
test is whether the *dual* theorems reuse the *same* instructions read on the
dual relation. They do: Mirsky and Dilworth are SEPARATE+COUNT with
"comparable" and "incomparable" swapped, and Dilworth's witness — the symmetric
chain decomposition — is a COUNT object whose count *is* its partition.

## The chain SEPARATE is the antichain SEPARATE, dualised

Sperner's SEPARATE: in an antichain, comparability is *forbidden*, so two
members at the same size could not both be present unless equal — really, the
layer map is injective on the antichain. The dual relation flips this. In a
*chain*, every two members are comparable, and comparability **forces a size
gap**: two comparable members of equal size coincide
(`ChainAntichain.chain_card_inj`, from `Sperner.eq_of_subseteq_card_eq`). This
is one instruction — "equal reading ⟹ equal object" — applied to the two dual
relations. From it:

  - the size map embeds any duplicate-free chain into the `n + 1` sizes
    `{0, …, n}`, so a chain has `≤ n + 1` members (`chain_length_le`), and the
    canonical chain `∅ ⊂ {0} ⊂ … ⊂ [n]` achieves it (`canonChain_max`);
  - the `n + 1` size-layers are themselves an antichain partition, each layer an
    antichain (`Sperner.kLayer_isAntichain`), and a chain meets each layer at
    most once (`chain_layer_cap`).

So longest chain `= n + 1 =` #layers `=` minimum antichain partition: **Mirsky**
(`mirsky_boolean`). The layers are simultaneously the obstruction (a chain can
pick one per layer) and the witness (they partition). That coincidence is the
SEPARATE instruction read on both relations at once.

## Dilworth's lower bound is COUNT, choice-free

The dual of Mirsky's lower bound: any cover of `2^[n]` by chains needs at least
as many chains as the largest antichain. Take the largest antichain we know —
the middle layer `kLayer n ⌊n/2⌋`, size `C(n, ⌊n/2⌋)` (`kLayer_card`). A chain
holds at most one middle-layer element (chain SEPARATE again), so assigning each
middle element to *a* chain that contains it is **injective**
(`dilworth_lower`). The assignment is `findChain` — the first chain in the cover
containing the element — a total, choice-free function (`memBL`/`findChain_spec`,
a `bif`-driven search, no `Classical`). Injectivity is `chain_card_inj`: if two
middle elements landed in the same chain they would be two comparable equal-size
members, hence equal. Counting the image: `C(n, ⌊n/2⌋) ≤ #chains`.

This is COUNT in its **injection** face (an injection into the cover bounds the
domain), the same primitive as the union/double-count faces, here read off the
choice-free `findChain`.

## The symmetric chain decomposition: a COUNT object whose count is its partition

The matching upper bound needs an *explicit* cover of exactly `C(n, ⌊n/2⌋)`
chains. The de Bruijn–Tengbergen–Kruyswijk construction builds one by recursion
on `n`, prepending the new coordinate at the front of each vector
(`ChainAntichain.scd`): a parent chain `C` spawns `extendC C` (new bit absent,
then present at the top — one level taller) and `raiseC C` (new bit present, top
dropped — one level shorter). Three obligations, each a witness:

  - **chain** — both constructors preserve the `subseteqB`-sorted order, so every
    member of `scd n` is a chain (`scd_isChain`).
  - **cover** — every length-`n` vector lies in some chain (`scd_cover`); with the
    chain property, `scd n` is a chain cover (`scd_chain_cover`).
  - **count** — `|scd n| = C(n, ⌊n/2⌋)` (`scd_card`). This is the rung where the
    construction earns its name, and it is pure COUNT.

The count is forced by a **symmetric-level invariant** (`scd_sym`): a chain's
sizes form a *centred contiguous run* `[k, k+1, …, n−k]` — in the run notation
`C.map cardB = consec k |C|` with `2k + |C| = n + 1`. The constructors shift the
run (`extendC_sym` extends it by one at the top, `raiseC_sym` drops the bottom
and shifts up), and the centring `2k + |C| = n+1` is preserved by a one-line Nat
identity (`raise_sum_arith`). A centred run straddles the middle level
`⌊n/2⌋` (`sym_span`: `k ≤ ⌊n/2⌋ ≤ n − k`), so **every chain contains exactly one
`⌊n/2⌋`-element** — one by existence (`scd_has_middle`, the run hits `⌊n/2⌋`),
at most one by the chain SEPARATE (`scd_middle_unique`).

"Exactly one middle element per chain" is the bridge from partition to count.
Collect the middle elements as a flattened trace
`flatMap (C ↦ C.filter (cardB = ⌊n/2⌋))`. Its length is `|scd n|` — one per
chain (`filter_len_one`, `length_flatMap213_const` at constant fibre `1`); it is
duplicate-free; and as a set it *is* the middle layer (every middle vector is in
some chain, every chain's middle vector has size `⌊n/2⌋` and length `n`). Two
duplicate-free lists with the same underlying set have equal length, so
`|scd n| = |kLayer n ⌊n/2⌋| = C(n, ⌊n/2⌋)` (`scd_card`).

## The partition is the crux, and it needs no injectivity

The trace is duplicate-free only because the SCD chains **partition** `2^[n]`:
distinct chains share no vector, and no chain is repeated. This is `scd_nodup`
together with `scd_same` — the positive form of disjointness: a vector shared by
two chains forces the chains to coincide. The proof is one induction on the
`bit :: tail` structure. Every child vector is `bit :: u` with `u` in the parent
(`mem_extendC`, `mem_raiseC`, `child_tail_mem`); a shared child vector therefore
forces the parents to share `u`, and the parents coincide by the induction
hypothesis. Within a single parent, `extendC` and `raiseC` are disjoint — the
only `true ::`-headed vector of `extendC` is its top, which `raiseC` drops
(`extendC_raiseC_disjoint`, using that a chain is duplicate-free,
`scd_chain_nodup`).

The lesson worth keeping: **no injectivity of `extendC`/`raiseC` was needed**.
`raiseC` is *not* injective in general (it forgets the top element), and the
naïve proof would stall trying to prove it is. The induction routes around this
— a collision between children of different parents is killed by the
*disjointness* hypothesis on the parents, not by inverting the constructors. The
partition hypothesis is strictly stronger than what raw injectivity could give,
and it is exactly what the next level consumes. With the partition in hand,
`scd n` is seen to carve `2^[n]` into `C(n, ⌊n/2⌋)` chains holding all `2^n`
subsets (`scd_flat_length`).

## Sperner three times: one COUNT face, three resolutions

The decomposition closes a loop. Sperner's number `C(n, ⌊n/2⌋)` is now reached
three independent ways on the one substrate:

  - **the double count** — `lym_double_count` collapsed by the middle-term
    minimum (`SpernerChains.sperner`);
  - **the named inequality** — LYM, then the same `min` step
    (`sperner_via_lym`);
  - **the partition** — an antichain meets each symmetric chain at most once
    (chain SEPARATE), so it injects into `scd n`; hence
    `|F| ≤ |scd n| = C(n, ⌊n/2⌋)` (`sperner_via_scd`).

The third is Dilworth ⟹ Sperner made constructive: the chain cover *is* the
certificate. That three compilations of one number share the SEPARATE+COUNT
instruction set, differing only in where they stop and which relation they read,
is the proof-ISA claim discharged on the chain/antichain duality.

## ISA instructions and witnesses

  - **SEPARATE** (`chain_card_inj`) — the antichain SEPARATE read on the dual
    relation: comparability forces a size gap.
  - **COUNT** — injection (`dilworth_lower`, `sperner_via_scd`), constant-fibre
    flatMap length (`scd_card`), set-equality length (`scd_flat_length`).
  - **New witnesses surfaced.** `scd_sym` (the symmetric-level invariant),
    `scd_same`/`scd_disjoint`/`scd_nodup` (the SCD partition without constructor
    injectivity), `scd_card`/`dilworth_boolean` (the count), `mirsky_boolean`,
    `sperner_via_scd`, `scd_flat_length`.

**Open rung.** None — Mirsky and Dilworth on `2^[n]` are closed ∅-axiom
(`ChainAntichain`, 84/84 PURE). The reusable substrate (the size-layer count
`C(n,k)`, the `subseteqB` order, the `flatMap213`/`nodup_flatMap213` enumeration
toolkit) carries over to the rest of the COUNT family.
