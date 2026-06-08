# Duality, in 213 — one transpose, not two theorems

A duality is not two theorems facing each other across a mirror. It is **one
instruction read on a relation and on its swap**, and the "duality theorem" that
the two sides agree is the statement that one incidence, read two ways, gives the
same count.

## 213-native answer

Take the **SEPARATE** instruction — "equal reading forces equal object"
(`Sperner.eq_of_subseteq_card_eq`). Read it on the relation *comparable*: an
antichain forbids comparability, so its members SEPARATE by size, and counting
the chains through them bounds the antichain (Sperner, `SpernerChains.sperner`).
Read the *same* instruction on the swapped relation *incomparable*: a chain
forces comparability, so comparable equal-size members coincide
(`ChainAntichain.chain_card_inj`), and the size-layers SEPARATE the chains —
Mirsky and Dilworth (`ChainAntichain.mirsky_boolean`, `dilworth_boolean`). The
dual pair *min chain cover* / *max antichain* is one number, `C(n,⌊n/2⌋)`,
because each is the same incidence counted along the other axis
(`theory/essays/proof_isa/chain_antichain_duality.md`).

## Derivation

The carrier of every COUNT duality is a single `0/1` incidence and the fact that
summing it by rows equals summing it by columns — `Sperner.sumOver_swap`, finite
Fubini. Sperner/LYM is that matrix (members × chains) read by columns (each chain
meets an antichain ≤ once) versus rows (each member lies on ≥ `|A|!(n−|A|)!`
chains); the equality of the two readings *is* the bound
(`theory/essays/proof_isa/lym_inequality.md`). The chain/antichain duality is the
same matrix transposed: the column cap and the row cap exchange roles when
*comparable* becomes *incomparable*. There is no second proof for the second
theorem — there is the one `sumOver_swap`, applied to the relation and to its
complement.

This is why "min = max" is not a coincidence to be explained but a reading to be
pointed at. `dilworth_boolean` packages exactly this: `scd n` is a cover of size
`C(n,⌊n/2⌋)` (one axis) and every cover is `≥ C(n,⌊n/2⌋)` (the other axis,
`dilworth_lower` via the choice-free `findChain`); the witness `scd` is a COUNT
object whose *count is its partition* (`scd_card` from the nodup middle-layer
trace).

## Dual function

Classically "duality" names a correspondence between two structures — a pairing,
a transpose, a Legendre / Pontryagin / LP swap — often carried by a separate dual
object and a separate proof. 213 strips the "two structures" packaging: the dual
object is the *same residue read by a Lens and by its swap*
(`seed/AXIOM/06_lens_readings.md`), and the duality theorem is the agreement of
the two readings, which for finite incidences is `sumOver_swap`. The refinement
is that 213 makes the "why they're equal" syntactic — not a deep correspondence
but Fubini on a 0/1 matrix, with a SEPARATE cap on each axis — so the content of
a duality is exactly *which relation you read and which cap holds*, nothing more.

## Cross-frame connections

The "one residue, swapped reading" shape recurs:

  - **comparable / incomparable** — SEPARATE read both ways (Sperner ↔
    Mirsky/Dilworth).
  - **rows / columns** — `sumOver_swap` = the incidence read both ways (the
    engine itself).
  - **`0` / `∞`** — one pre-Lens residue, not a dual pair of values; floor /
    boundary / center are Lens-artifacts (`seed/AXIOM/06_lens_readings.md` §6.9).
  - **magnitude / sign** — the difference-Lens reads a directed count-pair both
    ways (`seed/AXIOM/06_lens_readings.md` §6.7).

These are one fact at several resolutions: a "dual pair" is a Lens and its swap
on a single residue, never two independent things. And there is no privileged
"primal" side — no-exterior (`seed/AXIOM/05_no_exterior.md` §5.1) forbids ranking
one reading as *the* object; the residue is outside *every* view's image
(`Lens/FlatOntologyClosure.object1_not_surjective`), so neither the cover nor the
antichain is "the real one." `theory/lens/unified_equivalence.md` makes the
companion move for equivalence (four notions = decompositions of one
`Lens.refines` arrow); duality is the same economy applied to a relation and its
complement.

## Open frontier

The statement "every finite duality = `sumOver_swap` on a 0/1 incidence + a
SEPARATE cap per axis" is *witnessed* (Sperner, Mirsky, Dilworth, LYM, Bollobás
all instantiate it) but not *abstracted* into a single Lean theorem quantifying
over incidences and caps. Absent that abstraction,
"duality is one transpose" is a derived pattern across the witnesses, not a
proven meta-theorem.
