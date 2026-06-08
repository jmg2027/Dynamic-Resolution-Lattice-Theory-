# Reverse Mathematics 213 — the omniscience / axiom-cost ledger

Marathon field 17 (`blueprints/math/17_reverse_math_213.md`).  Status: **CORE CLOSED**
(Phases GA–GD, 22 PURE in `lean/E213/Lib/Math/Logic/`).

## The idea

Standard reverse mathematics calibrates a theorem by the set-existence axiom it needs,
over the base system `RCA₀`.  213 calibrates over the **residue's own carriers** — the
decision streams `Nat → Bool`, the binary digit tree, the self-cover `Object1` — and asks,
for each theorem, *which non-constructive decision does it cost?*  The decision in question
is always the same shape: **freeze an unending process into a finished verdict** — the
referent-capture the residue refuses (`theory/essays/foundations/the_one_diagonal.md`).
The ledger records, ∅-axiom, where that cost is zero and where it is an omniscience
principle.

## The carrier

A decision stream is `f : Nat → Bool` (a test, a predicate, a row of `Object1`).  An
**omniscience principle** claims to decide something infinitary about such a stream.  213
does not prove these; it states them as `Prop`s and calibrates everything against them
(`Lib/Math/Logic/Omniscience.lean`):

- **LPO** — `∀ f, (∃ n, f n = true) ∨ (∀ n, f n = false)` (the strongest base principle);
- **WLPO** — "everywhere false" is decidable as `∨ ¬`;
- **MP** — not-everywhere-false yields an explicit witness;
- **LLPO** — for an at-most-one-true stream, the true index is even or odd (weaker).

The structural implications hold ∅-axiom: `lpo_imp_wlpo`, `lpo_imp_mp`.

## The ledger spine (`reverse_math_ledger`, ∅-axiom)

| rung | result | cost |
|---|---|---|
| **free interior** | `cantor_stream_not_enumerable` — the Bool-stream carrier is not enumerable (Cantor's diagonal); the residue's `object1_not_surjective`; the p-adic `zpSeq_not_enumerable` | **none** |
| **omniscience base** | `lpo_imp_wlpo`, `lpo_imp_mp` | structural |
| **Π⁰₁ decision** | `lpo_decides_pi01` — deciding `∀n, h n = true`; instance `lpo_decides_infiniteBelow` (the König "infinite-below" predicate, via the native `existsLevel` recursion) | **LPO** |
| **König selection** | `lpo_infChildExistsN` — an infinite-below node has an infinite-below child, for a downward-closed (`LevelAntitone`) tree | **LPO** (LLPO suffices) |

`Lib/Math/Logic/Capstone.lean` bundles these into one ∅-axiom witness `reverse_math_ledger`.

## The phases

- **GA** `Omniscience.lean` — the principles + implications (6 PURE).
- **GB** `Pi01Decision.lean` — `lpo_decides_pi01`; `existsLevel` (level-existence Bool
  recursion); `lpo_decides_infiniteBelow` (5 PURE).
- **GB-cont** `ChildSelection.lean` — `lpo_infChildExistsN` (LPO + tree-monotonicity ⟹
  child selection); helpers `or_split`, `ne_true_imp_false`, `lpo_exists_false` (6 PURE).
- **GC** `DiagonalBase.lean` — `cantor_stream_not_enumerable` (the cost-0 base, 4 PURE).
- **GD** `Capstone.lean` — `reverse_math_ledger` (1 PURE).

## How the König thread arithmetized

König's lemma ("an infinite, finitely-branching tree has an infinite path") splits cleanly
on the residue carrier.  *Deciding* whether a node is infinite-below is a `Π⁰₁` statement
(`∀ n, existsLevel T s n = true`, the level body decidable by Bool recursion), so it costs
exactly **LPO**.  *Selecting* which child stays infinite is the genuinely König part: with
the tree downward-closed (`LevelAntitone`), LPO decides the left child, and if it is finite
it is empty beyond some depth, so — every depth being covered — the right child is infinite
(`lpo_infChildExistsN`).  The local compactness identity `WKL ⟺ Heine–Borel` lives next
door: `Lib/Math/Combinatorics/KonigConditional.infChildExists_iff_finiteSubcover` shows the
selection step and the finite-subcover step are equivalent modulo one omniscience decision.

## Pure-Lean notes

Everything is ∅-axiom (`#print axioms → empty`).  The recurring trap: core lemmas like
`Nat.succ_ne_zero` and the `if`/`split` machinery pull `propext` in this Mathlib-free
kernel.  Replacements used throughout: `Bool.noConfusion`, `Nat.noConfusion`, explicit
`cases`, and structural recursion.

## Connections

- `theory/essays/foundations/the_one_diagonal.md` — the one obstruction (Lawvere /
  Yanofsky) the free-interior base instantiates.
- `Lib/Math/Combinatorics/KonigConditional.lean` — the König νF bridge + the
  compactness ↔ König calibration the ledger formalizes.
- `Lib/Math/NumberSystems/Padic/NuEscape.lean` — the p-adic / 2-adic escapes (reached-by-none
  on the digit tree).
- Topology 213 (`Heine-Borel`), Logic / Proof Theory 213 (field 14) — neighbours.

## Open

- Bridge the native `existsLevel` to the ∃-form `KonigConditional.InfBelow`, and derive
  `LevelAntitone` from a downward-closed `T` (so the calibration speaks the König file's
  own predicate).
- Tighten the König-selection cost from LPO to LLPO (LLPO suffices; LPO is the upper bound
  used).
- The external reduction of the omniscience family (LLPO / WKL / fan) to a literal Lawvere
  fixed-point instance (the diagonal family is done).
- The fan theorem and bar induction as residue-native principles.
- Reconcile the ledger with `STRICT_ZERO_AXIOM.md` as the corpus-wide axiom-cost table.
