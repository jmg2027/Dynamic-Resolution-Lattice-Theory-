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

The structural implications hold ∅-axiom: `lpo_imp_wlpo`, `lpo_imp_mp`, and the clean
decomposition `lpo_iff_wlpo_and_mp` — **LPO ⟺ WLPO ∧ MP** (deciding "everywhere false"
plus extracting a witness).

## The ledger spine (`reverse_math_ledger`, ∅-axiom)

| rung | result | cost |
|---|---|---|
| **free interior** | `cantor_stream_not_enumerable` — the Bool-stream carrier is not enumerable (Cantor's diagonal); the residue's `object1_not_surjective`; the p-adic `zpSeq_not_enumerable` | **none** |
| **omniscience base** | `lpo_imp_wlpo`, `lpo_imp_mp` | structural |
| **Π⁰₁ / Σ⁰₁ decision** | `lpo_decides_pi01` (deciding `∀n, h n = true`; instance `lpo_decides_infiniteBelow`, the König "infinite-below" via `existsLevel`); `lpo_decides_sigma01` (deciding `∃n, h n = true`) | **LPO** |
| **König selection** | `lpo_infChildExistsN` — an infinite-below node has an infinite-below child, for a downward-closed (`LevelAntitone`) tree | **LPO** (LLPO suffices) |

`Lib/Math/Logic/Capstone.lean` bundles these into one ∅-axiom witness `reverse_math_ledger`.

## The phases

- **GA** `Omniscience.lean` — the principles + implications (6 PURE).
- **GB** `Pi01Decision.lean` — `lpo_decides_pi01`, `lpo_decides_sigma01`; `existsLevel` (level-existence Bool
  recursion); `lpo_decides_infiniteBelow` (5 PURE).
- **GB-cont** `ChildSelection.lean` — `lpo_infChildExistsN` (LPO + tree-monotonicity ⟹
  child selection); `levelAntitone_of_downwardClosed` (`existsLevel_pred` one-step-down by
  induction) discharges monotonicity from a downward-closed tree, giving
  `lpo_infChildExists_downwardClosed` (König selection for an actual Bool tree); helpers
  `or_split`, `or_intro_left/right`, `ne_true_imp_false`, `lpo_exists_false` (11 PURE).
- **GC** `DiagonalBase.lean` — `cantor_stream_not_enumerable` (the cost-0 base, 4 PURE).
- **GD** `Capstone.lean` — `reverse_math_ledger` (1 PURE).
- **GB-cont3** `KonigBridge.lean` — `infB_iff_infBelow` (native `InfB` = the ∃-form
  `KonigConditional.InfBelow`); pure `append_nil_pure`/`append_assoc_pure` (5 PURE).

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
`Nat.succ_ne_zero`, `List.append_nil`/`List.append_assoc`, the `if`/`split` machinery, and
`omega` all pull `propext` (and `omega` also `Quot.sound`) in this Mathlib-free kernel.
Replacements used throughout: `Bool.noConfusion`, `Nat.noConfusion`, `Nat.succ.inj`,
explicit `cases`, structural recursion, and hand-rolled pure lemmas
(`append_nil_pure`/`append_assoc_pure`).  A sharper obstacle: the Nat **literal** `+ 2` does
*not* definitionally reduce to `succ (succ ·)` (only `+ 1` does), so a `Bool`-recursion like
`parity (n + 2)` does not unfold — this is why `LPO ⟹ LLPO` (which needs even/odd parity)
does not close ∅-axiom without a custom pure Nat-arithmetic layer, and is left open.

## Connections

- `theory/essays/foundations/the_one_diagonal.md` — the one obstruction (Lawvere /
  Yanofsky) the free-interior base instantiates.
- `Lib/Math/Combinatorics/KonigConditional.lean` — the König νF bridge + the
  compactness ↔ König calibration the ledger formalizes.
- `Lib/Math/NumberSystems/Padic/NuEscape.lean` — the p-adic / 2-adic escapes (reached-by-none
  on the digit tree).
- Topology 213 (`Heine-Borel`), Logic / Proof Theory 213 (field 14) — neighbours.

## Open

- *(Done: `existsLevel` ↔ the ∃-form `KonigConditional.InfBelow` — `infB_iff_infBelow`,
  `KonigBridge.lean`; `LevelAntitone` from a downward-closed `T` — `levelAntitone_of_downwardClosed`.)*
- Tighten the König-selection cost from LPO to LLPO (LLPO suffices; LPO is the upper bound
  used).
- The external reduction of the omniscience family (LLPO / WKL / fan) to a literal Lawvere
  fixed-point instance (the diagonal family is done).
- The fan theorem and bar induction as residue-native principles.
- Reconcile the ledger with `STRICT_ZERO_AXIOM.md` as the corpus-wide axiom-cost table.
