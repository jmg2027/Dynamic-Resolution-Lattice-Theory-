# RE-RESEARCH registry — N_U removal

**Decision (Mingu Jeong, this session)**: eliminate the **N_U** concept.
Every conclusion that cited N_U as a premise is hereby marked **재연구
필요 (needs re-research)**.  Marking convention: **this central registry
only** — affected files are *not* annotated inline and keep building; the
re-derivation happens later, per item.

## What was removed vs kept

- **Removed**: the name `N_U` and its "universe constant / resolution
  limit value" framing — the privileged reading of `5²⁵` as *the*
  cardinality of the universe.  The Lean `abbrev N_U := configCount 2`
  and its dedicated theorems (`N_U_value`, `N_U_eq_d_pow_dsq`,
  `N_U_eq_configCount_two`) are deleted.
- **Kept (neutral math, unchanged)**: `configCountD d n := d^(d^n)` and
  its `d = 5` slice `configCount n` in
  `lean/E213/Lib/Math/Cohomology/Fractal/ConfigCount.lean`.  This is the
  bare combinatorial count of level-`n`, base-`d` configurations —
  parametric in both base and level, no privileged level.  Where a
  theorem genuinely asserts the *arithmetic* fact `configCount 2 = 5²⁵`
  (true), it is retained with N_U scrubbed from its name/statement.

## OPEN concept (deferred — research immature)

The original ask included "rename the fractal-level number to a *proper
concept*".  Per the originator: **the research on that topic is not yet
mature**, so no replacement concept/name is committed here.  Open
question for a future session:

> What, if anything, is the proper 213-native concept attached to the
> fractal-level configuration count `configCountD d n`?  Is there a
> non-arbitrary selected level, or is it purely parametric (Lens output)?
> `Theory.Atomicity.Five` selects `d = 5`; nothing selects a level.

Until resolved, `configCountD` stays as bare math; do **not** reintroduce
a "the universe number" reading.

## Dead spec

`seed/RESOLUTION_LIMIT_SPEC.md` is cited as canonical by ~20 files but was
**never committed** (no git history).  It is part of this immature topic.
Its citations are stale; resolve them only when the concept is redefined.

## Conclusions needing re-derivation (재연구 필요)

These were premised on `N_U = 5²⁵` as a privileged resolution cutoff.
The underlying arithmetic may survive; the *interpretive conclusion* must
be re-derived without the universe-constant premise.

### Physics — 1/α_em finitist derivation (headline result)
- `lean/E213/Lib/Physics/AlphaEM/GradedFormula.lean` — `1/α_em(IR) =
  60·S(N_U) + … + 1/(6·S_Wallis(N_U)⁵)`; the "ζ(2)=S(N_U), π appears
  nowhere" argument evaluates at resolution N_U.
- `lean/E213/Lib/Physics/AlphaEM/PiFiveGap.lean`
- `lean/E213/Lib/Physics/AlphaEM/Capstone.lean` (finitist closure with N_U)
- `lean/E213/Lib/Physics/AlphaEM/CupRingTrace.lean`
- `lean/E213/Lib/Physics/AlphaEM/NResolutionCandidates.lean`
- `lean/E213/Lib/Physics/AlphaEM/FractalLevelLift.lean`
- `lean/E213/Lib/Physics/AlphaEM/GramHigherOrder.lean`
- `lean/E213/Lib/Physics/AlphaEM.lean` (module overview)

### Physics — finitist / validation capstones
- `lean/E213/Lib/Physics/Foundations/FiniteUniverse.lean`
- `lean/E213/Lib/Physics/Foundations/NResolutionFromFractal.lean`
- `lean/E213/Lib/Physics/Foundations/FractalLensCardinality.lean` (K25 framing)
- `lean/E213/Lib/Physics/Capstones/FinitistObservableChain.lean`
- `lean/E213/Lib/Physics/Capstones/ValidationStandardOne.lean`
- `lean/E213/Lib/Physics/Capstones/PureAtomicObservables.lean`

### Math bridges that read 5²⁵ as "the resolution cutoff"
- `lean/E213/Lib/Math/GradedRingNUBridge.lean` (graded ring ↔ N_U bridge)
- `lean/E213/Lib/Math/UniverseChain/Synthesis.lean` (atomicity ⇒ N_U chain)
- `lean/E213/Lib/Math/UniverseChain/Universe.lean`, `Residue.lean`, `MobiusChain.lean`
- `lean/E213/Lib/Math/Padic/DRLT.lean`, `Padic/DRLTIntegration.lean`
- `lean/E213/Lib/Math/HodgeConjecture/Pairing/SignatureMetaTheorem.lean`
- `lean/E213/Lib/Math/Mobius213SignatureAxisCatalog{,Phase2}.lean`
- `lean/E213/Lib/Math/SignedCut/Level/Level25{Residual,Capstone}.lean`,
  `Level26Absence.lean`
- `lean/E213/Lib/Math/NumberGrid/{HorizontalAxis,FSMGradeTaxonomy}.lean`
- `lean/E213/Lib/Math/Information/{Entropy,Kolmogorov,Bit}.lean`
- `lean/E213/Lib/Math/DialogueAudit/{AxisDistinction,BitPrecision}.lean`
- (full list: `grep -rIlw N_U lean/ --include='*.lean'`)

### Narrative tiers (prose still says "N_U" — rewrite on re-derivation)
- `theory/` — 24 files (e.g. `theory/physics/foundations*.md`,
  `theory/lens/cardinality.md`, `theory/math/{hyper,universe_chain,
  padic_real213}.md`, `theory/essays/tower_atlas.md`).
- `catalogs/` — `atomic-integers.md`, `physics-constants.md`, `periodic-table.md`.
- `README.md`, `CLAUDE.md`, `STRICT_ZERO_AXIOM.md`, `LESSONS_LEARNED.md`.
- `seed/` — `INDEX.md`, `AXIOM/{03_form,06_lens_readings,99_history,INDEX}.md`,
  `CLOSED_FORM_SPEC.md`.

> Pervasive docstring/prose mentions of `N_U` in the above are left in
> place by design (central-registry-only marking).  Each gets rewritten
> when its conclusion is re-derived without the universe-constant premise.
