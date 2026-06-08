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

The structural implications hold ∅-axiom: `lpo_imp_wlpo`, `lpo_imp_mp`, the clean
decomposition `lpo_iff_wlpo_and_mp` — **LPO ⟺ WLPO ∧ MP** (deciding "everywhere false"
plus extracting a witness) — and `lpo_imp_llpo` — **LPO ⟹ LLPO** (the unique true index's
parity decides which half vanishes; `LLPO.lean`, via a native Bool `parity`).

## The ledger spine (`reverse_math_ledger`, ∅-axiom)

| rung | result | cost |
|---|---|---|
| **free interior** | `cantor_stream_not_enumerable` — the Bool-stream carrier is not enumerable (Cantor's diagonal); the residue's `object1_not_surjective`; the p-adic `zpSeq_not_enumerable` | **none** |
| **omniscience base** | `lpo_imp_wlpo`, `lpo_imp_mp` | structural |
| **Π⁰₁ / Σ⁰₁ decision** | `lpo_decides_pi01` (deciding `∀n, h n = true`; instance `lpo_decides_infiniteBelow`, the König "infinite-below" via `existsLevel`); `lpo_decides_sigma01` (deciding `∃n, h n = true`) | **LPO** |
| **König selection** | an infinite-below node has an infinite-below child, downward-closed tree — `lpo_infChildExistsN` (LPO) and the tightened `llpo_infChildExistsN` (LLPO) | **LLPO** (tight) |

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
- **GA-cont** `LLPO.lean` — `lpo_imp_llpo` (**LPO ⟹ LLPO**) via native `parity`,
  `even_or_odd`, `even_ne_odd` (8 PURE).
- **GB-cont4** `Interleave.lean` (6 PURE) + `LLPOSelection.lean` (12 PURE) —
  `llpo_infChildExistsN`: König child selection from **LLPO** (the tight cost), via the
  monotone turn-off encoding (`interleave`, `ftrue`, `ftrue_unique`, `not_both`).
- **GB-cont5** `WKLHeineBorel.lean` (5 PURE) — the global `WKL ⟺ Heine–Borel`, ∅-axiom
  half: `infPath_imp_infB` (a path ⟹ unbounded) and `bounded_imp_not_infPath` (bounded ⟹
  no path).  The WKL-strength half (unbounded ⟹ path) is *not* ∅-axiom — see below.

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
(`append_nil_pure`/`append_assoc_pure`).  Two subtleties found while closing `LPO ⟹ LLPO`
(the parity proof): (1) although the kernel stores the Nat **literal** `2` as a GMP value,
`n + 2`, `n + 1 + 1`, and `Nat.succ (Nat.succ n)` are nonetheless all definitionally equal
(`rfl`), so the `parity` `Bool`-recursion unfolds fine; (2) prefix `!` binds *looser* than
`=`, so `!(!b) = b` mis-parses as `!((!b) = b)` (silently a `decide`, which would pull
`propext`) — parenthesizing the left `!`-expression, `(!(!b)) = b`, fixes it.  With those,
`LPO ⟹ LLPO` closes ∅-axiom (`LLPO.lean`).

## The two ledgers — object-level vs meta-level axiom cost

The repo already keeps an axiom-cost ledger at the **meta level**: `STRICT_ZERO_AXIOM.md`
records, per theorem, which *kernel* axioms it pulls (`propext`, `Quot.sound`,
`Classical.choice`).  This marathon's ledger is the **object-level** twin: per math theorem,
which *omniscience principle* it costs (none / LPO / LLPO).  The two are one phenomenon read
at two scales, and the correspondence is exact:

> **Hypothesizing an omniscience principle at the object level is what keeps a theorem ∅
> at the meta level.**  If you tried to *prove* "decide this `Π⁰₁` predicate" inside Lean
> rather than take `LPO` as a hypothesis, you would reach for `Classical`/`decide`/`omega`
> — pulling `propext`/`Quot.sound` (`STRICT_ZERO_AXIOM` DIRT).  By carrying the omniscience
> principle as an explicit `Prop` argument, the cost is made **visible as a hypothesis**
> instead of **hidden as a kernel axiom**, and every theorem here stays PURE.

So the meta-level leaks catalogued this session — `omega` (`propext` + `Quot.sound`),
`Nat.succ_ne_zero`, `List.append_nil`/`append_assoc`, `if`/`split`, `decide`-on-a-`Prop` —
are precisely the points where an object-level omniscience cost would have leaked into the
kernel had it not been hypothesized or hand-rolled away.  The omniscience ledger is
`STRICT_ZERO_AXIOM.md` with the cost moved from the axiom line to the hypothesis line.

## Connections — and the external placement (Lawvere vs omniscience)

- `theory/essays/foundations/the_one_diagonal.md` — the one obstruction the free-interior
  base instantiates.  **External placement (honest):** the *diagonal* family
  (Cantor / Gödel / Russell / Tarski / Turing) is provably **one Lawvere fixed-point
  instance** (cartesian-closed self-reference).  The *omniscience* family (LPO / LLPO / WKL /
  fan) is **not** a Lawvere instance — it is the separate constructive-omniscience /
  Brouwerian-degree hierarchy (Bishop, Ishihara), about *deciding infinitary predicates*,
  not self-reference.  213 unifies them as the single *freeze-the-transition (capture)*
  move; the **external** mathematics keeps them in two distinct hierarchies, meeting only at
  realizability models.  Claiming "LLPO/WKL is a Lawvere instance" is the over-read to avoid.
- `Lib/Math/Combinatorics/KonigConditional.lean` — the König νF bridge + the compactness ↔
  König calibration the ledger formalizes.
- `Lib/Math/NumberSystems/Padic/NuEscape.lean` — the p-adic / 2-adic escapes.
- Topology 213 (`Heine-Borel`), Logic / Proof Theory 213 (field 14) — neighbours.

## Open

- *(Done — was the headline piece: König-selection cost tightened LPO → **LLPO**,
  `llpo_infChildExistsN`/`llpo_infChildExists_downwardClosed`, `LLPOSelection.lean`.  The
  monotone turn-off encoding on `Interleave.lean`: `g = interleave (ftrue fa) (ftrue fb)` is
  at-most-one-true via `ftrue_unique` (monotone ⟹ one rising edge, Nat trichotomy) +
  `not_both` (monotone + disjoint ⟹ not both rise); LLPO's even/odd split + `ftrue_all_false`
  gives `InfB s0 ∨ InfB s1`.  This was *not* a corollary of `lpo_imp_llpo` — a fresh proof.)*
- Global `WKL ⟺ Heine–Borel`, **WKL-strength half** (unbounded ⟹ infinite path, and ¬path ⟹
  bounded): *not ∅-axiom* — where WKL is **strictly stronger than LLPO**.  Local child
  selection is LLPO (`llpo_infChildExistsN`); iterating it into a *global* path needs
  **dependent choice** (turn the per-node selection disjunctions into a `step` oracle).
  Engine `KonigConditional.konig_conditional` (PURE) takes the oracle; building it is the
  gap.  The ∅-axiom *half* — path ⟹ unbounded, bounded ⟹ no path — is done
  (`WKLHeineBorel.lean`).
- The fan theorem and bar induction as residue-native principles.
- *(Done: `existsLevel` ↔ `KonigConditional.InfBelow` — `infB_iff_infBelow`; `LevelAntitone`
  from a downward-closed `T` — `levelAntitone_of_downwardClosed`; LPO ⟹ LLPO — `lpo_imp_llpo`;
  the two-ledger reconciliation with `STRICT_ZERO_AXIOM.md` — above; the external Lawvere
  placement — above.)*
