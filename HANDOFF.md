# Session Handoff — 2026-06-08 (the one-carrier program + the residue of the pointing)

## Branch / build
`claude/p-ary-spine-r-carrier-MPHbA`.  Full `lake build E213` ✓ clean; all new theorems
∅-axiom (`#print axioms` → "does not depend on any axioms").  No physics-constant changes
(pure mathematics / foundations).

## The arc, in one line
König branches, ℤ_p (every `p`), and ℝ all live on **one νF carrier**, with the full ring
arithmetic grounded in the real `Zp.add`/`Zp.mul`/`cutSum`/`cutMul` — and the deep insight that
**finite-state-ness (holonomicity) is a property of the *pointing*, not the *pointed-at*.**

## The unifying insight (the deep one)
There is **one non-surjection of a finite-stage cover, instantiated at three scales** — not three
analogous facts:

| the pointing | finite-stage cover | escapee (reached by none) | lemma |
|---|---|---|---|
| a **number** | `gToShape : Tree → GCoShape L` | the digit/cut/branch spine | `gspine_escapes` |
| an **operation**'s carry | the same map at `L = Nat` | `gspine (mulCarry)` | `carry_is_nu_escape` |
| a **description** | `Object1 : Raw → (Raw→Bool)` | the undifferentiated reading | `object1_not_surjective` |

The number-escape and operation-carry-escape are **literally two type-instances of one polymorphic
lemma** `gspine_one_carrier` (`L = Fin p` vs `L = Nat`).  "Holonomic / finite-state" = the predicate
"in the image of the finite-stage cover" — a property of the cover (pointing), never the inhabitant.
Witness: `(-1)² = 1` (`mul_carry_nu_residue`) — one inhabitant, two verdicts (trivial µF *result*,
unbounded νF *carry*).  The **unit** (`+` carry = the odometer bit, `add_carry_le_one`) and the
**residue** (`×` carry, unbounded νF, `mulCarry_unbounded`) are the two values that *one* carry
(`runCarry`, alphabet-independent) takes, decided by which cover reads it.  Narrative:
`theory/essays/foundations/the_one_carrier.md`.

## What is closed (all ∅-axiom)
- **Carrier** — `CoResidue.lean` §20 the label-generic spine `gspine : (Nat→L) → GCoShape L`
  (`boolSpine` = `L=Bool`); §21 the shift dynamics.  König / ℤ_p (`L=Fin p`) / ℝ (`L=Bool` cut-bits)
  all ride it (`padic_is_nu_escape`, `real_is_nu_escape`, `gspine_one_carrier`).
- **Arithmetic on the carrier** (`Padic/NuEscape.lean`, grounded in the real ring):
  - additive odometer `±1`, `(-1)+1=0` (`add_negOne_one_zero` = real `Zp.add`; `Odometer` §7–8);
  - valuation `× p = mulBase` = the genuine `Zp.mul`-by-`p` (`mulBase_eq_mul_pElem`; residue field 𝔽_p);
  - binary ring transported, 𝔽_p ring-hom readout (`padic_ring_on_carrier`, `residue_ring_hom`);
  - `+` finite-state (`add_carry_le_one`/`add_mealy_step`); `×` native corecursive (`mul_corecursive`:
    head `residue_mul`, tail `mulRaw_tail`) but NOT finite-state (`mulCarry_unbounded`);
  - the carry is itself a νF inhabitant (`carry_is_nu_escape`); `(-1)²=1` (`neg_one_sq_eq_one`).
- **ℝ on the carrier** (`Real213/NuEscape.lean`): `cutBits`/`cutNu`/`real_is_nu_escape`;
  `real_field_on_carrier` (cut-field `cutSum`/`cutMul` preserve the carrier).
- **Essay** `the_one_carrier.md` (foundations); frontier note `multiplicative_carry_residue.md`
  (core closed); helper `AddMod213.div_le_div_right_pure` (pure monotone div, core lacks it).

## Forward plan (multi-agent analysis, prioritized)
- **The schema frontier — ✅ RESOLVED (multi-agent dialectic).**  `CoResidue` §22
  `escape_by_invariant`: the abstract invariant-separation non-surjection, of which `gspine_escapes`
  (number- and operation-carry escapes, `gspine_escapes_via_schema`) is one instance.  **Cantor too**
  factors through it: `Lens.Cardinality.cantor_as_invariant` (∅-axiom), single cover-dependent
  separator `P_f φ := ∃ x, φ x = f x x`.  This **refuted** my earlier "Cantor is a sibling, not an
  instance / no single P" (committed in ae99493) — corrected across §22 docstring, essay, frontier
  note.  The genuine distinction is the **separator's self-reference**: cover-independent/intrinsic
  (`hasFloorPath`, *named*) vs cover-dependent/self-referential (`P_f`, *reached-by-none*).  Skeptic's
  residual: the schema unifies the final step; the diagonal *construction* of `P_f` is the
  cover-dependent content it consumes.  A genuine insight from continuous agent debate.
- **Meta-debate — "why does this kind of discussion recur?" (Structuralist vs Deflationist).**
  Outcome (Deflationist won the falsifiability point): the recurrence thesis is a *theorem* only at
  its checkable core (`cantor_general` — no surjective self-enumeration ⟹ no *closed/final*
  self-description; lint+catalog never terminate); the slide to "this particular debate happened
  *because* the diagonal re-entered" is unfalsifiable re-description (the repo's own
  Metaphysical-framing/Fog-jargon failure modes).  This session's specimen was ~mostly *contingent*
  (false "no single P", caught by exhibiting the witness + the ∅-axiom gate); the structural minimum
  is the one theorem.  Disciplined `why_the_reframing_recurs.md` with a "Falsifiability discipline"
  section (theorem vs narration) + de-self-sealed the self-check note.  The framework auditing its
  own central recurrence essay for §8 falsifiability.
- **A — RE-SCOPED (was top pick; agent over-claimed).**  `cut_decision_not_finite_state` as stated
  does NOT capture not-finite-state: `cutBits r N` reads only `r.xs N` (a memoryless transducer
  satisfies it), and for a fixed positive real `1/(N+1)→0` makes `cutBits r` *eventually constant*.
  ℝ's "transport-only / order-based" is an honest *prose* observation (kept in the essay), NOT a
  clean theorem.  A real ℝ-not-finite-state result needs a transducer / unbounded-modulus framework
  — a larger frontier, not a quick theorem.
- **B** — unify the omniscience ledger (field 17) with the finite-state ledger: none / Σ⁰₁-unbounded /
  LPO; operations and decisions are one cost (`the_omniscience_ledger`).  Now the top forward pick.
- **C** — cross-frame bridge: Casoratian `q=−1` (unit result, no finite depth, `DetSpectrumPoles`) =
  the sequence-scale mirror of `(-1)²=1`.  Both sides already proven → thin bridge.
- **Quick win** — `mulCarry (-1)(-1) (k+1) ≥ (k+1)(p-1)²/p` (immediate from `mulCarry_ge_mulRaw_div`
  + `mulRaw_negOne_negOne`); note the carry post-`/p` is not constant-difference, so
  `positive_linear_exact` applies to `mulRaw`, not directly to `mulCarry`.
- **Promotion** — the arc (CoResidue §20-22 + Odometer §7-8 + Padic/Real213 NuEscape + KonigConditional)
  → a `theory/math/numbersystems/` chapter; ℝ's "transport-only" stays honest prose (not a theorem),
  so promotion is not blocked.
- **Optional dedup** — fold `padic_additive_one_carrier` into `padic_arithmetic_one_carrier`
  (re-point essay+HANDOFF); kept for now (correct, different operand-focus).
- **Correction** — no Sₙ-sign/Leibniz-determinant infra exists (it is order-2 Casoratian), so
  "matrix-mult carry = det residue" is not near-term — reframed as C.

## Propext traps recorded (Mathlib-free kernel)
`Nat.succ_ne_zero` → `Nat.noConfusion`; `Nat.sub_add_cancel` → `cases p`/defeq; `Nat.zero_mod` →
`Nat.mod_eq_of_lt`; `Nat.div_self`/`add_div_right`/`div_lt_of_lt_mul` → `NatDiv213.*`;
`Nat.div_le_div_right` (absent) → `AddMod213.div_le_div_right_pure`; `Nat.add_sub_add_right` →
`Nat.succ_sub_succ`; core `div_add_mod` → `AddMod213.div_add_mod`; `by_cases` → `rcases Nat.lt_or_ge`;
`rw`-with-`Iff` → `.mp`/`.mpr`; base `a = a+0` → `(Nat.add_zero _).symm`.

## Decision recorded
`NuEscape.lean` (~830 lines) was considered for a 3-way split; **kept as one file** per CLAUDE.md
rule 7 (same-topic evolution → one file) + the `CoResidue.lean` (1245-line) precedent.  Header
rewritten to honest current scope; error-narration docstrings de-patchworked.

## Three-tier state
- Permanent: `lean/E213/` (all PURE) + `theory/essays/foundations/the_one_carrier.md`.
- Promotion candidate: the one-carrier sub-tree → `theory/math/numbersystems/` (after Advance A).
- Active scratchpad: `research-notes/frontiers/sequence_depth/multiplicative_carry_residue.md`.

## File map (this arc)
```
lean/E213/Theory/Raw/CoResidue.lean            ← §20 gspine (generic carrier), §21 shift dynamics
lean/E213/Theory/Raw/Odometer.lean             ← §7 runCarry, §8 p-ary odometer
lean/E213/Lib/Math/NumberSystems/Padic/NuEscape.lean  ← escape + arithmetic + multiplicative residue
lean/E213/Lib/Math/NumberSystems/Real213/NuEscape.lean ← ℝ on the carrier + cut-field closure
lean/E213/Meta/Nat/AddMod213.lean              ← + div_le_div_right_pure (pure monotone div)
theory/essays/foundations/the_one_carrier.md   ← the narrative (rewritten around the non-surjection)
research-notes/frontiers/sequence_depth/multiplicative_carry_residue.md ← frontier (core closed)
```
