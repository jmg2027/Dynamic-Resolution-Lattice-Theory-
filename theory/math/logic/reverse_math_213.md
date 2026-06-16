# Reverse Mathematics 213 — the omniscience / axiom-cost ledger

## Overview

Standard reverse mathematics calibrates a theorem by the set-existence axiom it
needs over the base system `RCA₀`.  213 calibrates over the **residue's own
carriers** — the decision streams `Nat → Bool`, the binary digit tree, the
self-cover `Object1` — and asks, for each theorem, *which non-constructive
decision does it cost?*  That decision is always the same shape: **freeze an
unending process into a finished verdict** — the referent-capture the residue
refuses (`theory/essays/foundations/the_one_diagonal.md`).  The chapter records,
∅-axiom, where the cost is zero and where it is an omniscience principle.

The cost is carried as an explicit `Prop` hypothesis, never proved.  This is the
object-level twin of `STRICT_ZERO_AXIOM.md`: hypothesizing an omniscience
principle at the object level is exactly what keeps a theorem ∅-axiom at the
meta level — the same cost, moved from the kernel-axiom line to the hypothesis
line (`theory/essays/methodology/the_omniscience_ledger.md`).

## Lean source

- **Umbrella**: `lean/E213/Lib/Math/Logic.lean`
- **Sub-tree**: `lean/E213/Lib/Math/Logic/` (10 files)
- **∅-axiom status**: **74 PURE / 0 DIRTY** (`python3 tools/scan_axioms.py E213.Lib.Math.Logic.*`)

| file | content | PURE |
|---|---|---|
| `Omniscience.lean` | `LPO/WLPO/MP/LLPO` + implications; `lpo_iff_wlpo_and_mp` | 6 |
| `Pi01Decision.lean` | `lpo_decides_pi01`/`_sigma01`, `existsLevel`, `lpo_decides_infiniteBelow` | 5 |
| `ChildSelection.lean` | `lpo_infChildExistsN`, `levelAntitone_of_downwardClosed`, `lpo_infChildExists_downwardClosed` | 11 |
| `DiagonalBase.lean` | `cantor_stream_not_enumerable` (the cost-0 base) | 4 |
| `Capstone.lean` | `reverse_math_ledger` (the spine in one witness) | 1 |
| `KonigBridge.lean` | `infB_iff_infBelow`; pure `append_nil_pure`/`append_assoc_pure` | 5 |
| `LLPO.lean` | `lpo_imp_llpo`, `wlpo_imp_llpo` via native `parity`, `even_or_odd`, `even_ne_odd` | 9 |
| `Interleave.lean` | div/mod-free `interleave`, `ftrue`, `ftrue_all_false` | 6 |
| `LLPOSelection.lean` | `llpo_infChildExistsN` (König selection from LLPO) | 12 |
| `WKLHeineBorel.lean` | `WKL ⟺ Heine–Borel`, `wkl_of_oracle`, `FanTheorem`/`Bar` | 13 |

## Narrative

A **decision stream** is `f : Nat → Bool` — a test, a predicate, a row of
`Object1`.  An **omniscience principle** claims to decide something infinitary
about such a stream.  213 states them as `Prop`s and calibrates everything
against them (`Omniscience.lean`):

- **LPO** — `∀ f, (∃ n, f n = true) ∨ (∀ n, f n = false)` (the strongest base);
- **WLPO** — "everywhere false" is decidable as `∨ ¬`;
- **MP** — not-everywhere-false yields an explicit witness (Markov);
- **LLPO** — for an at-most-one-true stream, the true index is even or odd (weaker).

The structural implications are ∅-axiom: `lpo_imp_wlpo`, `lpo_imp_mp`, the clean
decomposition `lpo_iff_wlpo_and_mp` (**LPO ⟺ WLPO ∧ MP** — deciding
"everywhere false" plus extracting a witness), and `lpo_imp_llpo`
(**LPO ⟹ LLPO** — the unique true index's parity decides which half vanishes,
via a native Bool `parity`).  The **middle strut** `wlpo_imp_llpo`
(**WLPO ⟹ LLPO**) completes `LPO ⟹ WLPO ⟹ LLPO`: applying WLPO to the even
substream `f(2k)` decides the parity verdict with only firing-*decidability* — the
negative alternative `¬(∀k, f(2k)=false)` is refuted *constructively* (build
`∀j, f(2j)=false` from an odd-true assumption), never by extracting a witness
(no Markov).  The residue's even/odd readout costs strictly less than its witness
readout.

**How the König thread arithmetized.**  König's lemma ("an infinite,
finitely-branching tree has an infinite path") splits cleanly on the residue
carrier.  *Deciding* whether a node is infinite-below is a `Π⁰₁` statement
(`∀ n, existsLevel T s n = true`, the level body decidable by Bool recursion),
so it costs exactly **LPO** (`lpo_decides_pi01`, `lpo_decides_infiniteBelow`).
*Selecting* which child stays infinite is the genuinely König part: with the
tree downward-closed (`LevelAntitone`, discharged by
`levelAntitone_of_downwardClosed`), LPO decides the left child, and if it is
finite it is empty beyond some depth, so the right child is infinite
(`lpo_infChildExistsN`).  The selection cost then **tightens to LLPO**
(`llpo_infChildExistsN`, `LLPOSelection.lean`) via the monotone turn-off
encoding on `Interleave.lean`: `g = interleave (ftrue fa) (ftrue fb)` is
at-most-one-true (`ftrue_unique` + `not_both`), and LLPO's even/odd split with
`ftrue_all_false` gives `InfB s0 ∨ InfB s1`.  This is a fresh proof, not a
corollary of `lpo_imp_llpo`.

**Local compactness.**  `WKLHeineBorel.lean` formalizes the global
`WKL ⟺ Heine–Borel`: the unconditional ∅-axiom half (`infPath_imp_infB`,
`bounded_imp_not_infPath`), the oracle-conditional WKL-strength half
(`wkl_of_oracle` — given the per-node selection oracle, unbounded ⟹ an infinite
path), the bundling `wkl_heineBorel_calibration`, and the **fan theorem** named
as the dual Brouwerian principle (`FanTheorem`/`Bar`, = HB proper) with the
clean `hasInfPath_of_stream`.  The local form lives next door in
`Lib/Math/Combinatorics/KonigConditional.infChildExists_iff_finiteSubcover`:
selection ⇒ compactness is free, compactness ⇒ selection costs one LLPO step.

## Key results

| Theorem | Lean module | Cost | Statement (informal) |
|---|---|---|---|
| `cantor_stream_not_enumerable` | `DiagonalBase` | **none** | the Bool-stream carrier is not enumerable (Cantor's diagonal) — the residue's `object1_not_surjective` |
| `lpo_iff_wlpo_and_mp` | `Omniscience` | structural | LPO ⟺ WLPO ∧ MP |
| `lpo_imp_llpo` | `LLPO` | structural | LPO ⟹ LLPO (native parity) |
| `lpo_decides_pi01` / `_sigma01` | `Pi01Decision` | **LPO** | LPO decides `∀n, h n` / `∃n, h n` |
| `lpo_infChildExistsN` | `ChildSelection` | **LPO** | LPO + tree-monotonicity ⟹ König child selection |
| `llpo_infChildExistsN` | `LLPOSelection` | **LLPO** | the tight cost — König selection from LLPO |
| `wkl_heineBorel_calibration` | `WKLHeineBorel` | LLPO + oracle | global `WKL ⟺ Heine–Borel` |
| `reverse_math_ledger` | `Capstone` | — | the spine bundled in one ∅-axiom witness |

## External placement (honest)

The *diagonal* family (Cantor / Gödel / Russell / Tarski / Turing) is provably
**one Lawvere fixed-point instance** (cartesian-closed self-reference;
`theory/essays/foundations/the_one_diagonal.md`).  The *omniscience* family
(LPO / LLPO / WKL / fan) is **not** a Lawvere instance — it is the separate
constructive-omniscience / Brouwerian-degree hierarchy (Bishop, Ishihara), about
*deciding infinitary predicates*, not self-reference.  213 unifies them as the
single *freeze-the-transition (capture)* move; the external mathematics keeps
them in two distinct hierarchies, meeting only at realizability models.  Claiming
"LLPO/WKL is a Lawvere instance" is the over-read to avoid.

## Research-note provenance

Field 17 (`blueprints/math/17_reverse_math_213.md`); readable book
`books/math/reverse-math-213.md`; methodology essay
`theory/essays/methodology/the_omniscience_ledger.md`.  No open field-17 source
note remains in `research-notes/`.

## Open frontier

By design external (named and isolated, not "to fix"):

- the bare **dependent choice** turning the per-node selection disjunctions into
  the `step` function (WKL proper, beyond LLPO) — carried as the `wkl_of_oracle`
  hypothesis;
- the **fan theorem** / **bar induction** (HB proper, Brouwerian) — named
  `FanTheorem`/`Bar`, with `hasInfPath_of_stream` done;
- HB proper (`¬HasInfPath ⟹ Bounded`) as an oracle/decision-conditional dual of
  `wkl_of_oracle`.

These are the precise reverse-math calibration: the gap *is* the omniscience
cost, hypothesized rather than hidden.

## How to verify

```bash
cd lean && lake build E213.Lib.Math.Logic
python3 tools/scan_axioms.py E213.Lib.Math.Logic.Omniscience E213.Lib.Math.Logic.Capstone \
  E213.Lib.Math.Logic.LLPOSelection E213.Lib.Math.Logic.WKLHeineBorel   # → N pure / 0 dirty
```
