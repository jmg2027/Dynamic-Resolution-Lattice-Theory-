# Session Handoff — 2026-06-08 (naming abstract concepts → 213; Reverse Mathematics 213 marathon)

## Branch
`claude/math-logic-career-path-khWPk` — pushed, well ahead of `origin/main`.
`cd lean && lake build` ✓ clean (full tree).  All new theorems ∅-axiom (PURE).
Working tree clean.

## What Was Done This Session

Theme (originator's math-logic vision): **what does standard math's "attaching a term to
an abstract concept" become under the 213 axiom?**  A reference-claim essay framed it; a
König/νF Lean arc + concept-pass + deep-research turned it into theorems; it then crystallised
into a full **Reverse Mathematics 213 marathon (field 17)** — the legibility bridge to
recognized mathematical logic.

### 1. Two permanent essays (theory/essays/foundations/)
- `the_reference_claim.md` — necessary/refused/under-test split.  Existence (`pointing ⟺
  residue`) is **transcendental necessity, not a thesis**; reference-closure necessary,
  referent-capture refused (`object1_not_surjective`), only *reach* under test.
- `the_one_diagonal.md` — the freeze-decision is **one** obstruction; re-dressing it is one
  more self-pointing (`residue_reentry_never_closes`).  Dual: Lawvere(1969)/Yanofsky(2003)
  unify Cantor/Gödel/Russell/Tarski/Turing; 213 makes the unifier the residue's self-cover.
  Math-scale twin of `why_the_reframing_recurs.md`.  Both registered in `theory/essays/INDEX.md`,
  logged in `promotion_essay_log.md` (row 13).

### 2. CLAUDE.md — "fog jargon" failure-mode row added
Hard language licensed only as **compression** (unfoldable on demand), never **fog**.

### 3. König νF bridge + compactness calibration — `Lib/Math/Combinatorics/KonigConditional.lean` (+9 PURE)
`konig_infinity_no_finite_raw`/`konig_infinity_is_nu_escape` (the König infinity is a νF
escape, no finite Raw).  `FiniteSubcoverOracle` + `infChildExists_iff_finiteSubcover`:
`WKL ⟺ Heine–Borel` *local* form on the residue carrier — NOT a naive iff (compactness ⇒
selection costs one LLPO child-disjunction decision).

### 4. p-adic νF escapes — `Lib/Math/NumberSystems/Padic/NuEscape.lean` (9 PURE)
`twoAdic_is_nu_escape` (ℤ₂ = a König binary-tree branch, no finite Raw); `zpSeq_not_enumerable`
(general `p ≥ 2`, native Cantor diagonal — pointwise, no `Cardinal`).

### 5. ★ Reverse Mathematics 213 marathon — field 17, CORE CLOSED (74 PURE / 10 files)
`blueprints/math/17_reverse_math_213.md` + INDEX field 17 (Phase G); book
`books/math/reverse-math-213.md`.  All ∅-axiom.  Calibrates each theorem by the omniscience
/ choice principle it costs, on the residue's carriers — Simpson-style reverse math done
213-native.  Files (`lean/E213/Lib/Math/Logic/`):
- `Omniscience.lean` (8) — `LPO/WLPO/MP/LLPO` + `lpo_imp_wlpo`, `lpo_imp_mp`,
  `lpo_iff_wlpo_and_mp` (**LPO ⟺ WLPO ∧ MP**), `wlpo_and_mp_imp_lpo`.
- `Pi01Decision.lean` (6) — `lpo_decides_pi01` (**LPO decides Π⁰₁**), `lpo_decides_sigma01`,
  `existsLevel`, `lpo_decides_infiniteBelow`.
- `ChildSelection.lean` (11) — `lpo_infChildExistsN` (LPO + tree-monotonicity ⟹ König
  child selection), `levelAntitone_of_downwardClosed`, `lpo_infChildExists_downwardClosed`.
- `DiagonalBase.lean` (4) — `cantor_stream_not_enumerable` (the **cost-0** base).
- `Capstone.lean` (1) — `reverse_math_ledger` (spine in one ∅-axiom witness).
- `KonigBridge.lean` (5) — `infB_iff_infBelow` (native `InfB`/`existsLevel` = the König
  file's ∃-form `KonigConditional.InfBelow`); pure `append_nil_pure`/`append_assoc_pure`.
- `LLPO.lean` (8) — `lpo_imp_llpo` (**LPO ⟹ LLPO**) via native `parity`.
- `Interleave.lean` (6) — div/mod-free even/odd `interleave` + `il_even`/`il_odd`, `ftrue`,
  `ftrue_all_false` (selection-from-LLPO infrastructure).
- `LLPOSelection.lean` (12) — **`llpo_infChildExistsN`**: König child selection from the
  weaker **LLPO** (monotone turn-off encoding; `ftrue_unique`, `not_both`).
- `WKLHeineBorel.lean` (13) — global `WKL ⟺ Heine–Borel`: unconditional half
  (`infPath_imp_infB`, `bounded_imp_not_infPath`), oracle-conditional WKL (`wkl_of_oracle`),
  `wkl_heineBorel_calibration`, and the **fan theorem** named (`FanTheorem`/`Bar`, the dual
  Brouwerian principle = HB proper) + `hasInfPath_of_stream`.

### 6. Concept-pass frontier notes (research-notes/frontiers/, registered in INDEX)
`naming_abstract_concepts.md`, `concept_compactness.md`, `concept_redressing_itself.md`
(deep-research, web-verified Lawvere/Yanofsky), `concept_function_space.md`.

## Current Precision Results (0 free parameters)
**No physics-constant changes** (pure mathematics / foundations).  See
`catalogs/physics-constants.md` for the standing DRLT table (α_em 0.09 ppb, etc.).

## Open Problems (Priority Order)
All under `blueprints/math/17_reverse_math_213.md` +
`research-notes/frontiers/naming_abstract_concepts.md`.

### 1. WKL/HB external pieces (by design not internal)
The bare dependent **choice** turning per-node selection disjunctions into the `step`
function (WKL proper beyond LLPO), and the **fan theorem** (HB proper, Brouwerian).  Both
are *named and isolated* (`wkl_of_oracle`/`FanTheorem`); the gap is by-design external —
this IS the precise reverse-math calibration.  Nothing to "fix"; only to hypothesize.

### 2. One-carrier p-ary νF escape
General `p` escape is done natively (`zpSeq_not_enumerable`) but on its own carrier; a
**p-ary spine in `Theory/Raw/CoResidue`** would put all `p` on the same νF carrier as
König/2-adic (only binary `boolSpine` exists).  Real CoResidue infra.

### 3. ℝ one-carrier with König
ℝ's reached-by-none is proved (`Analysis/Cauchy/DepthCeilingResidue.diag_not_in_seq`); a
dyadic bit-stream extractor from the `Real213` cut (`Nat → Nat → Bool`) would share the
`boolSpine` carrier.

### 4. More concept deep-dives (the systematic pass)
limit/completion, quotient/equivalence-class, actual-vs-potential infinity.  Each → its 213
reading.  Seeds in `naming_abstract_concepts.md`.

## Unresolved from This Session
No dead ends.  Two diagnosed-then-resolved traps worth remembering:
- **`LPO ⟹ LLPO` "Nat +2 wall" was a false alarm** — `n+2`, `n+1+1`, `succ(succ n)` ARE
  defeq (`rfl`); the real blocker was prefix `!` binding looser than `=` (`!(!b)=b`
  mis-parses to a `decide`).  Fix: parenthesize `(!(!b)) = b`.
- **propext-pulling tools in this Mathlib-free kernel** (avoid): `omega` (also `Quot.sound`),
  `Nat.succ_ne_zero`, `List.append_nil`/`append_assoc`, `if`/`split`, `decide`-on-`Prop`.
  Use `Bool.noConfusion`/`Nat.noConfusion`/`Nat.succ.inj`/`cases`/structural recursion +
  hand-rolled pure lemmas.

## Next
Field 17 is comprehensively closed.  Highest-value next: **(2)** the p-ary spine in
`CoResidue` (genuine new infra), or **promote** field 17 to a `theory/math/logic/` chapter
per `theory/PROMOTION_CRITERIA.md` (book exists in `books/math/`), or a **concept deep-dive**
(limit/completion).

## Three-tier state (per CLAUDE.md "Three-tier discipline")
- **Promotions this session**: `theory/essays/foundations/{the_reference_claim,the_one_diagonal}.md`.
- **Promotion candidates**: field 17 `Lib/Math/Logic/` (74 PURE, book written) → a
  `theory/math/` chapter is eligible.
- **Active scratchpad**: `research-notes/frontiers/` (4 concept-pass notes + field-17 frontier).

## File Map
```
theory/essays/foundations/the_reference_claim.md         ← essay (new)
theory/essays/foundations/the_one_diagonal.md            ← essay (new)
theory/essays/INDEX.md, research-notes/promotion_essay_log.md  ← registered + row 13
CLAUDE.md                                                ← + fog-jargon failure mode
lean/E213/Lib/Math/Combinatorics/KonigConditional.lean   ← +9 PURE (νF bridge + compactness calib)
lean/E213/Lib/Math/NumberSystems/Padic/NuEscape.lean     ← 9 PURE (2-adic + general-p escapes); +Padic umbrella
lean/E213/Lib/Math/Logic/*.lean                          ← field 17 (10 files, 74 PURE)
lean/E213/Lib/Math/Logic.lean                            ← Logic umbrella (10 files)
lean/E213/Lib/Math.lean                                  ← imports Logic umbrella
blueprints/math/17_reverse_math_213.md, blueprints/math/INDEX.md  ← field 17 blueprint + Phase G
books/math/reverse-math-213.md                           ← marathon book (field 17)
research-notes/frontiers/{naming_abstract_concepts,concept_compactness,
    concept_redressing_itself,concept_function_space}.md ← concept-pass notes (+INDEX)
```
