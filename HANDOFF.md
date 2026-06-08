# Session Handoff — 2026-06-08 (naming abstract concepts → 213; Reverse Mathematics 213 marathon)

## Branch
`claude/math-logic-career-path-khWPk` — `origin/main` merged in (131 commits: the
determinant / permutation-sign stack, Ollivier–Ricci, transcendentals/PDE ladders, etc., now
present alongside this session's work).  `rm -rf .lake/build && lake build` ✓ clean (forced
fresh), `layer_audit` 0 violations / 1839 files, `kernel_regress` 45/45 0-axiom, purity
0 sorry/axiom/native_decide/Classical/Mathlib.  **READY TO MERGE → main.**

## What Was Done This Session

Theme (originator's math-logic vision): **what does standard math's "attaching a term to
an abstract concept" become under the 213 axiom?**  A reference-claim essay framed it; a
König/νF Lean arc + concept-pass + deep-research turned it into theorems; it then crystallised
into a full **Reverse Mathematics 213 marathon (field 17)** — the legibility bridge to
recognized mathematical logic.  A closing **merge marathon** then ran: merge `origin/main`
→ `/process` (sink decouple) → `/essay` (`the_omniscience_ledger`, caps field 17) →
`/org-audit` (INDEX counts) → `/purity-check` (clean) → `/ready-to-merge` (READY).

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

### 2. One-carrier p-ary νF escape — ✅ CLOSED (this session)
`CoResidue.lean §20`: the **label-generic spine** `gspine : (Nat→L) → GCoShape L` keeps the
binary König branch structure, leaf-labelled by an arbitrary alphabet `L`.  `boolSpine` is the
`L=Bool` instance (`boolSpine_eq_gspine`), `lToShape = gToShape true false`.  General-`p` ℤ_p
rides the `L=Fin p` instance: `Padic/NuEscape.padic_is_nu_escape` (every `p ≥ 2`).  So all `p`
share one carrier.  All ∅-axiom.

### 3. ℝ one-carrier with König — ✅ CLOSED (this session)
`Real213/NuEscape.lean`: the **cut-decision bit-stream** `cutBits : Real213 → (Nat→Bool)` (the
`orderProj` diagonal, ∅-axiom decidable, read off the approximants) rides the existing
`boolSpine` carrier.  `real_is_nu_escape` — a constructive real is reached by no finite Raw, on
the *same* `SlashNu` carrier as König / 2-adic / p-adic; `real_cut_distinct` faithful on cut
bits.  So König / ℤ_p / ℝ all sit on one νF carrier.

### 3b. Arithmetic odometer lift — ✅ CLOSED (this session)
`Odometer.lean` §7 `runCarry` (the alphabet-independent adding-machine carry; binary carry is the
`g=f` instance) + §8 the **p-ary odometer** `pOdo` on `Nat→Fin p`: `pcarry_dies_iff_has_floor`
(µF/νF mirror), `pOdo_allTop_zero` (`(-1)+1=0`), `pOdo_injective` (no collision).  `Padic/NuEscape`
capstone `padic_arithmetic_one_carrier`: ℤ_p's `-1` (= `ZpSeq.neg_one`, all digits `p-1`) is the
all-top stream whose `+1`-carry never lands and wraps to `0` — so the one-carrier claim is
*algebraic* (the residue unit `+1`), not only dynamical.

### 3c. Multiplicative valuation on the carrier — ✅ CLOSED (this session)
`Padic/NuEscape` `padic_valuation_one_carrier`: the multiplicative generator `× p` (`mulBase` =
prepend-`0` digit) is the valuation operator — `p·x ∈ pℤ_p`, `v_p(p·x)=1+v_p(x)`
(`mulBase_valAtLeast_succ`, against the existing `Norm.Zp.valAtLeast`), injective, residue field
𝔽_p (`residue`, surjective; `1 ∉ pℤ_p`), and **`÷p` = the carrier shift** (`mulBase_coRight`,
CoResidue §21).  So the carrier carries ℤ_p's valuation *filtration* (the multiplicative norm
skeleton).

### 3d. `mulBase` IS the ring `× p` — ✅ CLOSED (this session)
`Padic/NuEscape` `mulBase_eq_mul_pElem`: the existing full `Zp.mul` (digit convolution + carry,
`Arith.lean`) applied to the element `p` (`pElem`, digit 1 at position 1) equals `mulBase`
pointwise — because **multiplication by `p` carries nothing** (`mulCarry_pElem = 0`: each
convolution term is one digit `< p`), collapsing to the shift.  So the carrier's `× p` is the
genuine ring operation, not a stand-in.  **Open**: `×` as a *binary* op on `gspine` (general
`x·y`); ℝ's field on the carrier.

> Note: `Nat.zero_mod` also pulls `propext` (use `Nat.mod_eq_of_lt hp` for `0 % p = 0`).

### 3e. Additive grounding + `shiftLeft` reconciliation — ✅ CLOSED (this session)
Repo-first: `mulBase` IS the existing `Zp.shiftLeft … 1` (`mulBase_eq_shiftLeft`) — the cons-
presentation of the existing `×p^k` shift, kept for cleaner spine defeq.  Real-ring additive
grounding: `add_negOne_one_zero` — `Zp.add (neg_one) (one) = 0` at the digit level (carry is `1`
from position 1, `add_negOne_one_carry`), so the abstract odometer overflow
(`padic_succ_negOne_eq_zero`, via `pOdo`) is the genuine `Zp.add`-by-`one`
(`padic_additive_one_carrier`).  So **both** `+` (`Zp.add`) and `×p` (`Zp.mul`) on the carrier are
grounded in the existing ring.  **Open**: `×` as a binary op on `gspine`; ℝ field on the carrier.

> Note: `Nat.div_self` and `Nat.add_div_right` pull `propext`; use `NatDiv213.mul_div_self_pure`
> (`1*p/p=1` ⟹ `p/p=1`) for `p/p=1`.

### 3f. Binary `×` on the carrier — ✅ CLOSED (this session)
`Padic/NuEscape` `padic_ring_on_carrier`: the carrier escapes are closed under `×` and `+` (spine
of `x·y`/`x+y` reached by no finite Raw), and the residue-field readout `residue : ℤ_p ↠ 𝔽_p` is a
**ring hom** — `residue_mul` (`residue(x·y) = x₀·y₀ mod p`, carry-free at position 0), `residue_add`,
`residue_ring_hom` (respects `+`,`×`,`0`,`1`).  So the binary `×` of the real `Zp.mul` lives on the
one carrier (transport), with a genuine 𝔽_p ring-map.

### 3g. Native addition (finite-state) vs transport-only × — ✅ CLOSED (this session)
`Padic/NuEscape` `padic_native_addition`: **addition is native** — `Zp.add`'s carry is always a
single bit (`add_carry_le_one`: digit pairs sum `< 2p`), a one-bit-state Mealy machine
(`add_mealy_step`); the carry bit = the odometer bit.  **Multiplication is not finite-state** (the
convolution reads all lower digits, `mulCarry` unbounded) — so `×` is transport-only *by nature*,
resolving the "native product" frontier structurally (holonomic/non-holonomic at the ring-op
scale).  **Open**: ℝ field on the carrier (the only remaining one-carrier frontier).

> Note: `Nat.div_lt_iff_lt_mul` and core `Nat.div_lt_of_lt_mul` pull `propext`/`Classical`; use
> `NatDiv213.div_lt_of_lt_mul` (pure).

### 3h. ℝ field on the carrier — ✅ CLOSED; one-carrier program COMPLETE
`Real213/NuEscape` `real_field_on_carrier`: ℝ's cut-table field ops (`cutSum`/`cutMul`, `Sum/CutSum`
+ `Mul/CutMul`) preserve the carrier — the diagonal spine of `cutSum cx cy`/`cutMul cx cy` is reached
by no finite Raw (`cutTableNu`/`cutTable_is_escape`).  So ℝ is a `+`/`×`-closed carrier subset like
ℤ_p.  **Honest structural limit (by-design, not a gap)**: ℝ's cut is order-decision-based and
presentation-dependent, so — unlike ℤ_p's faithful digit carrier — it admits *no* finite-state
native op and *no* ring-hom readout; its field is irreducibly transport-only.  This closes every
named one-carrier frontier (carrier, shift, additive ±1, multiplicative valuation, binary ×, native
finite-state characterization, ℝ field).

> Note (propext traps hit + recorded): `Nat.succ_ne_zero`, `Nat.sub_add_cancel`, `by_cases`, and
> `rw`-with-an-`Iff` all pull `propext`.  Use `Nat.noConfusion`, `cases p`/defeq, `rcases
> Nat.lt_or_ge`, and `.mp`/`.mpr` via defeq instead.

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
Field 17 closed; one-carrier program closed (p-ary spine + ℤ_p + ℝ all on the one νF carrier,
this session).  Highest-value next: **promote** field 17 to a `theory/math/logic/` chapter per
`theory/PROMOTION_CRITERIA.md` (book exists in `books/math/`), or a **concept deep-dive**
(limit/completion), or a `theory/` narrative for the §20 one-carrier result.

## Three-tier state (per CLAUDE.md "Three-tier discipline")
- **Promotions this session**: `theory/essays/foundations/{the_reference_claim,the_one_diagonal}.md`,
  `theory/essays/methodology/the_omniscience_ledger.md`.
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
