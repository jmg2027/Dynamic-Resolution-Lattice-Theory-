# Naming an abstract concept — what it is under the 213 axiom

**Deep-research candidate** (originator: Mingu Jeong, this session).  Status: open
frontier; one concrete instance closed in Lean (König), two sibling theorems queued.

## Core research question

When standard mathematics **attaches a term to an abstract object** — "ℕ", "ℝ",
"ℚ_p", "the limit", "the completion", "countable / uncountable", "the set of all
functions" — what *exactly* is that act under the 213 axiom?

**Working answer (this session, to be tested across the catalog below):** naming is a
residue-internal Lens event (`naming_is_internal`) that names a **generation rule** (a
fold / coalgebra), *never the completed totality*.  The "abstract / infinite" content of
the named thing is the **νF escape** — reached by no finite stage (`object1_not_surjective`,
`reached_by_none.md`).  And the classical "complete it / decide it" steps are one single
**∞-decision** (the *capture* move), which 213 either **refuses** or **carries as an
explicit input** — never silently performs.

So the act of naming splits, every time, into three modal parts (the
`the_reference_claim.md` split):

| part | what it is | example |
|---|---|---|
| **necessary** | the reference itself (you named it → it's a residue-internal Lens event); the rule is finite | "ℝ" names the cut/modulus rule |
| **refused** | capturing the referent as a completed/decided object | "ℝ as a finished set you decide membership/cardinality of" pulls choice/LEM |
| **under test** | reaching the named thing by internal handles without forcing an exterior | ε-δ existential vs explicit modulus |

The conjecture this frontier tests: **every** abstract-concept naming in standard math
decomposes this way, and the "where does the import hide" question always lands on the
same single ∞-decision.

## Established this session (the spine)

1. **The reference-claim essay** — `theory/essays/foundations/the_reference_claim.md`:
   existence (`pointing ⟺ residue`) is transcendental necessity, not a thesis; the open
   edge is *reach* (how far internal handles go before an exterior is forced).

2. **König νF bridge — CLOSED, ∅-axiom** (`Lib/Math/Combinatorics/KonigConditional.lean`,
   +5 PURE this session): the infinite branch König decides about is a νF inhabitant
   (`konigBranchNu` via `boolSpineSlashNu`) and is reached by **no finite Raw**
   (`konig_infinity_no_finite_raw`).  Capstone `konig_infinity_is_nu_escape`: given the
   König hypotheses the branch lies in `T` at every finite stage **and** is a νF escape.
   So "which Raw chunk is the König infinity?" → *none*; it is the escape.

3. **ℝ / ℚ_p / König are one shape, different branching** (read-through, not yet a single
   theorem):

   | | tree | branches/level | native rep | where the ∞-decision hides |
   |---|---|---|---|---|
   | **ℝ** (`Real213`) | dyadic (binary) | 2 | Dedekind cut on dyadics (+ dyadic-stream bridge) | ε-δ existential `∃δ` (vs explicit `modulus`) |
   | **ℚ_p** (`Padic`) | p-ary | p | digit stream `ℕ → Fin p` | first-nonzero-digit / valuation search (vs `invGeneral`'s supplied `v`) |
   | **König** (general) | finitely-branching | finite | path `List Bool` + νF branch | which-child-is-infinite (`InfChildExists`, left unproved) |

   All three: **number = νF escape** (no finite prefix reaches it); held as a *generation
   rule* (transition — the cut/modulus, the carry FSM, the oracle) and **never frozen**
   into a decided object.  The classical "complete/decide" step is the same single move in
   three costumes — and each library handles it identically: **carry the certificate as
   input, do not decide.**  `Real213` uses explicit modulus instead of ε-δ; `Padic`'s
   `invGeneral` takes the valuation `v` as input (the chapter states plainly: an arbitrary
   sequence's first nonzero digit "cannot be found by a pure search" — *that is the
   König/InfBelow ∞-decision, left as input, not smuggled*).

4. **Countable / uncountable is a property of the branching rule, read off the finite
   rule** — not a captured cardinal.  The repo refuses "ℝ uncountable" as a `Cardinal`
   theorem (pulls choice/propext); it states an injection preserving distinctness
   (`boolSpine_injects_bitstreams`).  One-output-per-step (ℕ) = enumerable = countable;
   choice-per-step (ℝ, ℚ_p) = tree = not enumerable (Cantor) = uncountable.

## Deep-research seeds (the systematic pass — the actual candidate)

Run each standard abstract-concept naming through: *which Lens? which fold-level
(proposition vs proof, §5.3)? capture vs reference? where is the ∞-decision? what is the
νF escape?* — producing either a theorem (like the König bridge) or a precise reading.

- **ℕ** — the count-Lens / successor rule.  Mostly clear; pin as the "thin branch
  (one output/step) = countable" base case, sibling to the ℝ/ℚ_p bridges.
- **ℝ, ℚ_p** — the two bridges below; write `real_is_nu_escape`, `padic_is_nu_escape`.
- **"the limit" / "the completion"** — the diagonal-of-the-approximants (`reached_by_none.md`
  three-move method); naming the limit = naming νF + its anamorphism, not a point.
- **"compactness" / König / WKL** — **deep-dive done** (`concept_compactness.md`):
  compactness of the dyadic interval = König's binary lemma = the *same* `InfChildExists`
  import (not a new wall, the König wall on the space side); "compact" in 213 = (νF
  refinement rule) + (explicit total-boundedness modulus).  Theorem seed:
  `FiniteSubcoverOracle ↔ InfChildExists` ∅-axiom (reverse-math `WKL ⟺ Heine–Borel` on the
  νF carrier).  The reverse-math calibration angle (`STRICT_ZERO_AXIOM.md` as an axiom-cost
  ledger) starts here.
- **"cardinality (countable/uncountable)"** — the branching-rule reading above; the honest
  injection-not-Cardinal form.
- **"quotient / equivalence class"** — the Lens-arrow (`theory/lens/unified_equivalence.md`);
  naming "ℝ as ℚ/Cauchy mod ∼" = naming a Lens.refines, where raw `=` would need funext
  (a Lens artifact, cf. `ZpSeqEquiv`).
- **"the set of all functions / the powerset" / "∀,∃ over an infinite domain"** — where the
  capture move is most tempting; expected to land on the refused bucket + a νF carrier.
- **"actual vs potential infinity"** — the frozen/dynamic (§5.7) reading: no external time
  axis ⇒ both are Lens readings; "actual infinity" = freezing the transition (the capture
  /import); "potential infinity" = the rule kept open (the allowed transition).

## Next concrete step (code) — partly closed

Mirror the König bridge for the number systems, unifying ℝ/ℚ_p/König under one
`boolSpine_escapes`-style pattern:
- **ℚ_p (2-adic) — CLOSED, ∅-axiom** (`Lib/Math/NumberSystems/Padic/NuEscape.lean`,
  4 PURE): a `ZpSeq 2` is a νF inhabitant (`twoAdicNu` via `boolSpineSlashNu`) reached by
  **no finite Raw** (`twoAdic_is_nu_escape`) — same `boolSpine_escapes` shape as
  `konig_infinity_no_finite_raw`.  `Fin 2 ≃ Bool`, so a 2-adic integer *is* literally a
  branch of König's binary tree.
- **ℝ — already on record**: the dyadic real's reached-by-none is closed
  (`theory/essays/foundations/reached_by_none.md`; `Analysis/Cauchy/DepthCeilingResidue`,
  `diag_not_in_seq`).  The native `Real213` carrier is the cut `Nat → Nat → Bool` (not a
  single `Nat → Bool` stream), so a one-carrier-with-König unification would need a dyadic
  bit-stream extractor — open polish, not a gap (the escape itself is proved).
- **ℚ_p general `p` — open**: needs a `Fin p`→bits encoding or a p-ary spine in
  `CoResidue` (the binary `boolSpine` is the only spine so far).

So "ℚ_p (p=2) / König infinity are literally the same escape" is now a theorem; the ℝ and
general-`p` one-carrier unifications are the remaining polish.

## Anchors

- `theory/essays/foundations/{the_reference_claim, reached_by_none, the_form_of_the_residue,
  the_residue_as_primitive}.md`
- `Lib/Math/Combinatorics/KonigConditional.lean` — König νF bridge (5 PURE this session)
- `Theory/Raw/CoResidue.lean` — νF carrier (`SlashNu`, `boolSpineSlashNu`, `boolSpine_escapes`)
- `theory/math/numbersystems/{real213, padic_real213}.md`
- `Lens/{NoExteriorClosure.naming_is_internal, FlatOntologyClosure.object1_not_surjective}`
- `seed/AXIOM/05_no_exterior.md` §5.3 (proposition/proof fold-level), §5.4 (the under-test
  guard), §5.7 (frozen/dynamic); `06_lens_readings.md` §6.5–6.6 (0/∞, state=state-transition)
- Companion for the deep-research pass: the `/deep-research` skill; the calibration angle
  ties to `frontiers/research_grade_closure_gate.md` (axiom-cost ledger).
