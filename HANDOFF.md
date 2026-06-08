# Session Handoff — 2026-06-08 (the one-carrier program + the residue of the pointing; merge marathon)

## Branch
`claude/p-ary-spine-r-carrier-MPHbA` — `origin/main` merged in (98 commits: the CKM CP-phase /
Zolotarev / spiral-axis / determinant-sign stacks).  Ahead 103.  `rm -rf .lake/build && lake build
E213` ✓ clean (fresh); `layer_audit` 0 violations / 1877 files; `kernel_regress` 45/45 0-axiom;
purity 0 sorry/axiom/native_decide/Classical/Mathlib.  **READY TO MERGE → main.**

## The arc, in one line
König branches, ℤ_p (every `p`), and ℝ all live on **one νF carrier**, with the full ring
arithmetic grounded in the real `Zp.add`/`Zp.mul`/`cutSum`/`cutMul` — and the deep insight that
**finite-state-ness (holonomicity) is a property of the *pointing*, not the *pointed-at*.**

## What Was Done This Session

### 1. The one-carrier program (all ∅-axiom)
- **Carrier** — `CoResidue.lean` §20 label-generic spine `gspine : (Nat→L) → GCoShape L` (`boolSpine`
  = `L=Bool`); §21 shift dynamics.  König / ℤ_p (`L=Fin p`) / ℝ (`L=Bool` cut-bits) all ride it
  (`padic_is_nu_escape`, `real_is_nu_escape`, `gspine_one_carrier`).
- **Arithmetic on the carrier** (`Padic/NuEscape.lean`, grounded in the real ring): additive odometer
  `±1` (`add_negOne_one_zero` = real `Zp.add`; `Odometer` §7–8); valuation `× p = mulBase` = the
  genuine `Zp.mul`-by-`p` (`mulBase_eq_mul_pElem`); binary ring + 𝔽_p ring-hom readout
  (`padic_ring_on_carrier`, `residue_ring_hom`); `+` finite-state (`add_carry_le_one`); `×` native
  corecursive (`mul_corecursive`) but NOT finite-state (`mulCarry_unbounded`); the carry is itself a
  νF inhabitant (`carry_is_nu_escape`); `(-1)²=1` (`neg_one_sq_eq_one`).
- **ℝ on the carrier** (`Real213/NuEscape.lean`): `cutBits`/`real_is_nu_escape`/`real_field_on_carrier`.

### 2. The non-surjection schema (CoResidue §22) — multi-agent dialectic
`escape_by_invariant` — the abstract invariant-separation non-surjection; `gspine_escapes` (number +
operation-carry escapes) is one instance.  **Cantor too** factors through it
(`Lens.Cardinality.cantor_as_invariant`, single cover-dependent separator `P_f φ := ∃x, φ x = f x x`).
`diag_via_modifier` — the construction-level root (Cantor = point-dependent modifier; invariant =
constant modifier).  The genuine distinction = **separator self-reference** (cover-independent /
*named* vs cover-dependent / *reached-by-none*).  A Unifier-vs-Skeptic debate refuted an earlier
"Cantor is a sibling, not an instance" claim with the machine-checked factoring.

### 3. Methodology discipline (multi-agent debates)
`why_the_reframing_recurs.md` given a **"Falsifiability discipline"** section: the recurrence thesis
is a theorem only at its checkable core (`cantor_general` — no closed self-description); "this debate
happened *because* the diagonal re-entered" is unfalsifiable re-description (the repo's own
Metaphysical-framing/Fog-jargon failure modes).  A Fog-auditor vs Compression-defender debate
confirmed 5/6 of the session's hard phrases are genuine compression (pin to ∅-axiom theorems); the
one fog residue was stripped.

### 4. Merge marathon (this session's closing)
merge `origin/main` → `/process` (1 sink decouple) → promote (one-carrier → `padic_real213.md`
chapter, log row 36) → cross-domain note (branch × main) → `/essay`
(`finite_state_is_of_the_pointing`, log row 37) → `/org-audit` (INDEX 94/19/14/7/73, clean) →
`/purity-check` (clean) → `/ready-to-merge` (READY).

## Current Precision Results (0 free parameters)
**No physics-constant changes** in this branch's work (pure mathematics / foundations).  Main's
merged CKM CP-phase / α_em table stands in `catalogs/physics-constants.md`.

## Open Problems (Priority Order)
### 1. The cross-scale unifier (×-carry ↔ Casoratian depth)
A single ∅-axiom term with both the p-adic carry (`mulCarry_unbounded`) and the Casoratian depth
(`cas_neg_unit_no_finite_depth`) as instances of "unit value, non-finite-state pointing".
Frontier: `research-notes/frontiers/one_carrier_crossdomain.md` + `.../sequence_depth/multiplicative_carry_residue.md`.

### 2. ℝ not-finite-state — needs a transducer / unbounded-modulus framework
`cutBits r N` reads only `r.xs N` (eventually constant per real), so ℝ's "transport-only" is honest
prose, NOT a clean theorem.  Frontier: `research-notes/frontiers/sequence_depth/multiplicative_carry_residue.md`.

### 3. Multiplication's unit/non-unit = finite-state/escape (Zolotarev ↔ ×p)
`× unit` = a finite permutation with a sign (`mulPermMod`, main) vs `× p` = the valuation escape
(`mulBase`, branch).  Frontier: `research-notes/frontiers/one_carrier_crossdomain.md`.

### 4. Lens §6.7 readout of the carry; exact-linear `mulCarry ≥ c·k`
Frontier: `research-notes/frontiers/sequence_depth/multiplicative_carry_residue.md` (soft-open).

## Unresolved from This Session
No dead ends.  Honest corrections made: the "Cantor is a sibling, not an instance" claim was refuted
(now `cantor_as_invariant`); "Advance A" (ℝ not-finite-state) was found over-claimed and re-scoped to
honest prose.  Propext traps recorded (Mathlib-free kernel): `Nat.succ_ne_zero`→`Nat.noConfusion`;
`Nat.sub_add_cancel`→`cases p`; `Nat.zero_mod`→`Nat.mod_eq_of_lt`; `Nat.div_self`/`add_div_right`/
`div_lt_of_lt_mul`→`NatDiv213.*`; `Nat.div_le_div_right` (absent)→`AddMod213.div_le_div_right_pure`;
`Nat.add_sub_add_right`→`Nat.succ_sub_succ`; core `div_add_mod`→`AddMod213.div_add_mod`; `by_cases`→
`rcases Nat.lt_or_ge`; `rw`-with-`Iff`→`.mp`/`.mpr`; base `a=a+0`→`(Nat.add_zero _).symm`.

## Next
Highest-value: the cross-scale unifier (Open Problem 1) — one term with `mulCarry`-unbounded and the
Casoratian depth as instances.  Or unify the omniscience ledger (field 17) with the finite-state
ledger (operations and decisions are one cost).  Or a concept deep-dive (limit/completion).

## Three-tier state (per `CLAUDE.md` "Three-tier discipline")
- **Promotions this session**: one-carrier number-system results → `theory/math/numbersystems/padic_real213.md`
  (§ "The one νF carrier", log row 36); essay `theory/essays/synthesis/finite_state_is_of_the_pointing.md`
  (row 37); foundations essay `theory/essays/foundations/the_one_carrier.md` (this arc).
- **Promotion candidates**: none outstanding from this branch.
- **Active scratchpad**: `research-notes/frontiers/{one_carrier_crossdomain, sequence_depth/multiplicative_carry_residue}.md`.

## File Map
```
lean/E213/Theory/Raw/CoResidue.lean              ← §20 gspine, §21 shift, §22 escape_by_invariant/diag_via_modifier
lean/E213/Theory/Raw/Odometer.lean               ← §7 runCarry, §8 p-ary odometer
lean/E213/Lib/Math/NumberSystems/Padic/NuEscape.lean   ← escape + carrier arithmetic + multiplicative residue
lean/E213/Lib/Math/NumberSystems/Real213/NuEscape.lean ← ℝ on the carrier + cut-field closure
lean/E213/Lens/Cardinality/Cantor.lean           ← + cantor_as_invariant (Cantor factors through the schema)
lean/E213/Meta/Nat/AddMod213.lean                ← + div_le_div_right_pure (pure monotone div)
theory/essays/foundations/the_one_carrier.md     ← the one-carrier narrative (one non-surjection)
theory/essays/synthesis/finite_state_is_of_the_pointing.md  ← branch×main cross-scale synthesis
theory/essays/methodology/why_the_reframing_recurs.md  ← + Falsifiability discipline section
theory/math/numbersystems/padic_real213.md       ← + "The one νF carrier" section (promotion)
research-notes/frontiers/one_carrier_crossdomain.md          ← branch×main cross-domain note
research-notes/frontiers/sequence_depth/multiplicative_carry_residue.md ← the carry frontier (core closed)
```
