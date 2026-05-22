# G120 — N_U re-derivation plan

**Round 3 sharpened version (2026-05-22 evening).**  Earlier Round
2 hybrid retracted per user observation (§9 Round 3): the name
`N_U` itself is the universe-constant framing import; correct fix is
demote to `abbrev` (or inline) atop a parametric family
`configCount : Nat → Nat`.  See §4 + §9 for the diagnosis chain.

## §1 Diagnosis (current state)

- **Three syntactically distinct definitions of `N_U` coexist and agree
  only by `decide`**: `Lib/Math/ResolutionLimit.lean` (`d^(d*d)`),
  `Lib/Math/UniverseChain/Universe.lean` (`5^25` literal), and
  `Lib/Physics/Foundations/NResolutionFromFractal.lean` (`d^numV`).
  Equality is numerical, not structural.
- **Two of four spec framings have no Lean derivation**: `tensorDOF`
  is docstring-only (no Tensor type, no rank predicate; `d^(d*d) = N_U`
  reduces to `rfl`), and `injProjSpace` has zero witness anywhere in
  `lean/E213/`.
- **`ResolutionInvariant` (in `ResolutionLimit.lean`) has four fields,
  three filled by `:= N_U` placeholders with rfl-agreement**, even
  though `fractalLens` and `coloringK25` each have a real external
  derivation (`NResolutionFromFractal.n_resolution_eq_hierarchy`,
  `FractalLensCardinality.K25_coloring_count_eq_N_U`).  The record
  hides actual content behind cosmetic identity.
- **Load-bearing decide-chain**: `d^(d*d) = 298023223876953125` is
  consumed by every ValidationStandard capstone
  (`ValidationStandardOne`, `FinitistObservableChain`,
  `PureAtomicObservables`, `AlphaEM/Capstone`,
  `AlphaEM/NResolutionCandidates`, `AlphaEM/FractalLevelLift`).
  Breaking the literal value breaks the precision cascade.
- **`numV` is overloaded**: `V25.lean` defines `numV : Nat := 25`
  (iteration-count framing A); `Fractal/Level.lean` defines
  `numV (L : Nat) : Nat := 5^L` (self-referential framing B).  Same
  name, different shape, bridged only by `decide` on `L = 2`.

## §2 Goal (target state — Round 3 sharpened)

After execution:

1. **Canonical object is a parametric family**:
   `configCount : Nat → Nat` (vertex / configuration count at fractal
   level n), built on existing `Cohomology/Fractal/Level.lean`'s
   `numV (L : Nat) : Nat := 5^L`.  `5^25` is the value at level 2,
   not a privileged constant.
2. **`N_U` demoted to display-name `abbrev`** (or deleted entirely):
   `abbrev N_U : Nat := configCount 2`.  No `def N_U` anywhere.
   Three current `def N_U` instances collapse to this single
   `abbrev` (or are inlined to `configCount 2` directly).
3. **`ResolutionInvariant` record DELETED**.  The 4 framings were
   not 4 independent derivations — they were 4 verbal relabellings
   of a single family value (`fractalLens` = "configurations at
   level 2"; `coloringK25` = "configurations at level 2 named after
   the bipartite graph"; `tensorDOF` = "configurations at level 2
   named after rank-2 tensor"; `injProjSpace` = missing entirely).
   Critic's Option (e) adopted; Round 3 sharpening confirms.
4. **(B) self-referential framing** becomes a `theorem` ABOUT the
   family: `numV (d*d) = d^(d*d)` is a property of the family at the
   special point n = d² = 25, not a separate framing.
5. **`numV` name collision resolved**: keep parametric `numV (L : Nat)
   := 5^L` (Level.lean) as canonical; `V25.lean`'s constant `numV := 25`
   becomes either a theorem `numV_at_2 : Level.numV 2 = 25` or is
   inlined where used.
6. **ValidationStandard cascade unchanged**: consumer literals
   `298_023_223_876_953_125` still resolve via `decide` to
   `configCount 2`.  Only the *naming path* changes — the literal
   value is preserved.
7. **d generalization hook open**: `configCount` is parametric in
   the level; making it also parametric in `d` (base of the
   fractal) is a one-line extension if/when future research needs it.

## §3 Phases (Round 3 sharpened — 6 phases)

### Phase 1 — Establish parametric `configCount` family

- **Scope**: introduce or canonicalize the parametric Lens output.
- **Decision**: use `Cohomology/Fractal/Level.lean`'s existing
  `numV (L : Nat) : Nat := 5^L` as the family of "vertex count at
  level L".  Add `def configCount (n : Nat) : Nat := d ^ (numV n)`
  in a canonical home (probably new file
  `Lib/Math/Cohomology/Fractal/ConfigCount.lean` or appended to
  `Lib/Math/ResolutionLimit.lean`).
- **Effort**: 1 hr.
- **Depends on**: nothing.

### Phase 2 — Demote `N_U` to `abbrev`; collapse three defs

- **Scope**: drop privileged status of `N_U`.
- **Files changed**:
  - `Lib/Math/ResolutionLimit.lean`: change `def N_U : Nat := d^(d*d)`
    to `abbrev N_U : Nat := configCount 2`.
  - `Lib/Math/UniverseChain/Universe.lean`: delete `def N_U := 5^25`;
    use `ResolutionLimit.N_U` (the abbrev) or inline `configCount 2`.
  - `Lib/Physics/Foundations/NResolutionFromFractal.lean`: keep
    `n_resolution_candidate` only as a *local* convenience; replace
    with theorem `n_resolution_candidate_eq : n_resolution_candidate
    = configCount 2`.
- **Success**: `grep -rn "^def N_U" lean/E213/` returns 0 hits;
  `grep -rn "^abbrev N_U" lean/E213/` returns ≤ 1 hit.
- **Effort**: 1 hr.
- **Depends on**: Phase 1.

### Phase 3 — Delete `ResolutionInvariant` record (Critic Option e)

- **Scope**: dismantle the 4-way convergence fiction.
- **Files changed**: `Lib/Math/ResolutionLimit.lean`.
- **Decision**:
  - Delete `structure ResolutionInvariant` + `resolutionInvariantWitness`
    entirely.
  - Move the 2 real derivations (`fractalLens`-equivalent and
    `coloringK25`-equivalent) to standalone lemmas:
    - `theorem fractal_iter_two_count : configCount 2 = NResolutionFromFractal.n_resolution_candidate`
    - `theorem coloring_K25_count : configCount 2 = FractalLensCardinality.K25_coloring_count`
  - `tensorDOF` and `injProjSpace`: simply **gone**.  No replacement.
- **Files changed**: `Lib/Math/ResolutionLimit.lean`,
  `STRICT_ZERO_AXIOM.md` (update categorization).
- **Success**: no `ResolutionInvariant` in codebase; 2 standalone
  bridging lemmas exist; `lake build` clean.
- **Effort**: 1-2 hr.
- **Depends on**: Phase 2.

### Phase 4 — Recast (B) self-referential as family-theorem

- **Scope**: dissolve the special-framing claim.
- **Decision**:
  - Delete `def universe_level := d * d` from
    `NResolutionFractalDepth.lean` (it was a wrapper for `d * d`).
  - Replace with a `theorem numV_at_d_squared : numV (d * d) = d ^ (d * d)`
    stated as a property of the family (a numerical fixed-point
    observation at the special level n = d² = 25).
  - This makes the (A) iteration-count framing and the (B) self-ref
    framing into ONE thing: the configCount family + a theorem about
    its behaviour at a special point.
- **Files changed**: `NResolutionFractalDepth.lean`.
- **Success**: `grep -rn "universe_level" lean/E213/` returns 0 hits
  (the wrapper is gone); the self-ref theorem stands as a family
  property.
- **Effort**: 1 hr.
- **Depends on**: Phase 1.

### Phase 5 — Resolve `numV` collision

- **Scope**: keep parametric `numV` as canonical; demote constant.
- **Decision**:
  - Keep `Cohomology/Fractal/Level.lean`'s
    `def numV (L : Nat) : Nat := 5^L` as the canonical parametric
    family.
  - Inline `V25.lean`'s `def numV : Nat := 25` to `Level.numV 2`
    everywhere (it was just the parametric form evaluated at L=2).
    Delete the constant `def` or convert to
    `theorem numV_at_2 : Level.numV 2 = 25 := rfl`.
- **Files changed**: `V25.lean` + any callers using its `numV`.
- **Success**: `grep -rn "^def numV" lean/E213/` returns exactly 1 hit
  (the parametric one in Level.lean).
- **Effort**: 1 hr.
- **Depends on**: Phase 1.

### Phase 6 — Audit + ValidationStandard cascade preservation

- **Scope**: regression-test the consumer cascade.
- **Files NOT changed**: ValidationStandard capstones, AlphaEM
  capstones — their `decide`-chains on `5^25` literal value should
  resolve unchanged.
- **Success**:
  - `cd lean && lake build` clean
  - `python tools/scan_axioms.py` PURE on all touched modules
  - `lake build E213.Lib.Physics.Capstones.ValidationStandardOne`
    succeeds (decide-chain preserved)
  - `#print axioms configCount` / `#print axioms N_U` clean
- **Effort**: 1 hr.
- **Depends on**: Phases 1-5.

**Total mean effort**: ~6-7 hr.  Critic-flagged tail risk: 8-12 hr if
ValidationStandard cascade surfaces a hidden `decide`-shape
dependency.

## §4 Resolution (Round 3 sharpened — clean Option (c))

**Round 2 hybrid retracted.**  Earlier draft chose hybrid (a + c.phase3)
to neutralize D's downstream-cascade risk + C's universe-constant
smell simultaneously.  Critic flagged hybrid as "indecision encoding";
Round 3 user sharpening confirmed: the *name* `N_U` is itself the
problem (carries universe-constant connotation per CLAUDE.md
"Universe-constant framing" failure mode), and the 4-way convergence
was never 4 independent derivations but a single family-value
relabeled 4 ways.

**Adopt clean Option (c) + Critic's Option (e)**: demote `N_U`,
promote the *parametric family* `configCount : Nat → Nat`, and
**delete `ResolutionInvariant` entirely**.

### How this resolves earlier concerns

- **D's cascade risk**: still neutralized.  Consumer-site literals
  `5^25` / `298_023_223_876_953_125` remain.  Only the *naming
  path* changes from `N_U` to `configCount 2` — the literal value
  resolves identically via decide.  ValidationStandard capstones
  untouched.
- **C's universe-constant smell**: fully eliminated.  No constant
  named `N_U` privileged; just a Nat-valued family + a display
  abbrev.
- **Critic's "delete record entirely"**: adopted.  4-way claim was
  fiction (1 value × 4 verbal relabels).
- **d ≠ 5 generalization hook**: open by construction.  Family is
  parametric in `n`; making it also parametric in `d` is a one-line
  extension.

### Why earlier hybrid was wrong

The hybrid kept `ResolutionInvariant` to "honor C's record-stays
but-with-real-proofs intuition" while keeping `def N_U` to "honor
D's preserve-decide-chain intuition".  But:
- The record was never useful — the 2 real framings can be
  standalone lemmas.
- `def N_U` carries the failure-mode-flagged name; `abbrev` (or
  inlined `configCount 2`) accomplishes the same decide-chain
  preservation without the privileged constant.

The empirical risk (D) was real but addressable without the
privileged name.  The frame import (C, critic) was the actual
blocker.  Round 3 sharpening (the user) reframed: the family is
the natural object, the name was the import.

## §5 Risks + mitigations

- **Risk**: removing `tensorDOF` field breaks a downstream consumer
  that pattern-matches on the record shape.
  **Mitigation**: grep for `.tensorDOF` before deletion; D's audit says
  no structural consumers exist outside the record file itself.
- **Risk**: Phase 2 import cycle (`ResolutionLimit` is upstream of
  `NResolutionFromFractal`).
  **Mitigation**: move the wiring into a new
  `Lib/Math/ResolutionLimitProofs.lean` downstream module; keep
  `ResolutionLimit.lean` definition-only.
- **Risk**: rename in Phase 4 breaks `V25.lean` clients silently.
  **Mitigation**: rename the parametric one (fewer callers) and run
  `lake build` after each file.
- **Risk**: framing (B) self-reference disappears as a concept.
  **Mitigation**: it's not in the spec; archive any narrative to
  `research-notes/archive/` rather than promoting.
- **Risk (critic-surfaced)**: docstrings or §1 summaries silently
  re-import "universe constant" framing during cleanup.  Cleanup is
  *especially* prone because canonicalization invites the import.
  **Mitigation**: every docstring touch in this plan must be
  reviewed against CLAUDE.md "Universe-constant framing" failure mode.
  N_U descriptions stay as "count-Lens output at fractal level 2",
  not "the resolution limit" or "the system constant".
- **Risk (critic-surfaced)**: `PureAtomicObservables` brands itself
  "no N_U dependence" while `FinitistObservableChain` shares N_U.
  Plan deliberately papers over by saying "both compile".
  **Mitigation**: §8 Open question lists this; plan does not silently
  resolve.  Either branding is wrong, or they are different observable
  classes — out-of-scope here but explicitly flagged.
- **Risk (critic-surfaced)**: tail effort beyond 30-min mean.  A hidden
  `decide` chain that depends on specific reduction shape might break
  under canonicalization.  **Mitigation**: Phase 5 audit runs the full
  validation-standard build; if cascade breaks, extend Phase 1-2
  before merging.  Worst-case estimate: 4-8 hr.
- **Risk (critic-surfaced)**: hardcoded `5^25` baked into consumer
  literals prematurely closes generalization (d ≠ 5, level ≠ 2).
  **Mitigation**: §8 Open question records this; do not refactor
  consumer literals to non-parametric form in this plan.

## §6 Success criteria (Round 3 sharpened)

1. `grep -rn "^def N_U" lean/E213/` returns **0** hits.
2. `grep -rn "^abbrev N_U" lean/E213/` returns at most 1 hit (or 0 if inlined).
3. `grep -rn "^def numV" lean/E213/` returns exactly 1 hit (parametric in Level.lean).
4. `grep -rn "ResolutionInvariant" lean/E213/` returns 0 hits (record gone).
5. `grep -rn "universe_level" lean/E213/` returns 0 hits (def gone).
6. `def configCount : Nat → Nat` exists in canonical home.
7. `cd lean && lake build` clean.
8. `python tools/scan_axioms.py` PURE on all touched modules.
9. ValidationStandard capstones build unchanged (decide-chain preserved):
   - `ValidationStandardOne`
   - `FinitistObservableChain`
   - `PureAtomicObservables`
   - `AlphaEM.Capstone`
   - `AlphaEM.NResolutionCandidates`
   - `AlphaEM.FractalLevelLift`
10. `#print axioms configCount`, `#print axioms N_U` (if abbrev kept) →
    "does not depend on any axioms".
11. The 2 retained bridging lemmas (`fractal_iter_two_count`,
    `coloring_K25_count`) cite their external derivations and are PURE.

## §7 Out of scope (Round 3 sharpened)

- **Restoring `N_U` as a `def`** — explicitly forbidden.  `abbrev`
  or inline only.  The name carries universe-constant connotation
  (CLAUDE.md "Universe-constant framing" failure mode); making it a
  `def` re-imports the frame.
- **Re-introducing `ResolutionInvariant` or similar 4-way records** —
  the 4-way claim was fiction (1 family-value × 4 relabels).  If
  future research finds genuinely independent derivations of
  `configCount 2`, they enter as standalone lemmas, not as a
  catch-all record.
- **Adding tensor or injProj framings** as Lean theorems.  No work
  in current scope.  If a real `Tensor` type or injective-projection
  cardinality bound emerges later, it gets a standalone lemma —
  not a re-instantiated `ResolutionInvariant`.
- **`PureAtomicObservables` vs `FinitistObservableChain` orientation
  reconciliation** — orthogonal to N_U structure.  Open for a separate
  note if it surfaces.
- **`catalogs/constants.md` numerics** — preserved as-is (the value
  is the same; only the path through Lean is changed).
- **d ≠ 5 generalization execution** — the *hook* is opened by the
  parametric family, but the actual `d` parametrization is deferred
  pending genuine research need.
- **Docstring claims silently re-importing "the resolution limit"**
  framing — every docstring touched in this plan must be reviewed
  against the universe-constant failure mode.  Phrasings like "the
  resolution limit value", "the system invariant" are forbidden.

## §8 Open questions

- Should `Universe.N_U` (in `UniverseChain/Universe.lean`) remain as a
  structure field at all, or be replaced by a projection to the
  canonical `ResolutionLimit.N_U`?  Defer until Phase 1 callers are
  mapped.
- Is there a structural (non-`decide`) proof that the fractal
  derivation and the K_{3,2}^{(c=2)} coloring count agree, or is
  `decide` the only available bridge?  If the latter, document it as
  a numerical coincidence at the spec layer, not a structural identity.
- Does `PureAtomicObservables`'s "no `N_U` dependence" framing need
  reconciliation with `FinitistObservableChain`'s opposite orientation,
  or are they genuinely two different observable classes?  Open for
  G121 if it surfaces during Phase 2 wiring.
- **Consumer-site literal generalization** — Round 3 sharpening
  opens `configCount` parametrically in level, but consumer sites
  still hardcode `5^25` value.  If d ≠ 5 generalization research
  emerges, those literals need parametric rewrite.  Not part of
  this plan.
- **Option (e) adopted** — Round 3 confirmed: `ResolutionInvariant`
  fully deleted (was Critic's recommendation, Round 2 plan
  rejected, Round 3 plan accepts).
- **Self-referential framing's structural justification** — the
  theorem `numV (d*d) = d^(d*d)` (Phase 4) is currently a
  numerical fixed-point observation via `decide`.  Whether there's
  a *structural* (non-`decide`) proof that the family fixed-points at
  level d² (a deep self-reference fact) remains open.  If found, it
  would be a non-trivial property of the configCount family.

## §9 Debate trace (multi-agent provenance)

This plan was produced by a 2-round multi-agent debate on branch
`claude/research-notes-organization-Gr3Tp` (2026-05-22).

### Round 1 — four parallel agents

| Agent | Angle | Key finding |
|---|---|---|
| A | Inventory | 258 hits across `lean/E213/`; 3 redundant `N_U` definitions; 3 of 4 ResolutionInvariant fields are placeholders; 2 of 4 spec framings have no Lean witness |
| B | Derivation audit | fractalLens/coloringK25 PROVEN externally but record uses bare placeholder; tensorDOF is docstring-only (rfl identity); injProjSpace MISSING; (A)/(B) `numV` framings same-named different-function |
| C | Restructuring proposal | Voted Option (d) hybrid: §8-clean Lens-output framing + per-framing theorems; framing (B) may need archiving |
| D | Downstream risk | Voted Option (a): risk asymmetry sharp (25 value-only consumers survive any change); ValidationStandard decide-chain load-bearing; (a) costs ~30 min, (c) costs 1-2 days |

C voted (d), D voted (a) — divergence.

### Round 2 — synthesizer + critic in parallel

- **Synthesizer**: produced this plan, picking **hybrid (a + Phase 3 of c)** — single canonical def (D's path) with surgical removal of placeholder fields (C's concern absorbed).
- **Critic**: identified 6 weakness categories.  Specifically:
  - §8.4 frame-import risk during cleanup itself (universe-constant residue, before/after dichotomy)
  - Load-bearing assumptions silently retained (PureAtomic orientation, numV unification)
  - Effort underestimation (tail risk 4-8 hr, not 30 min mean)
  - Argued for picking (c) cleanly over hybrid; called hybrid "indecision encoded"
  - Surfaced **Option (e)**: delete ResolutionInvariant entirely (only 2 framings are real)
  - Future-proof hook: d ≠ 5 generalization

### How critic concerns were absorbed

| Critic concern | Plan response |
|---|---|
| Universe-constant residue during cleanup | §5 new risk + mitigation; explicit docstring discipline |
| PureAtomic vs Finitist orientation conflict | §8 open question; explicitly NOT silently resolved |
| Tail-risk effort | §5 new risk acknowledges 4-8 hr worst case |
| numV unification structural depth | §8 open question on structural-vs-decide bridge |
| Option (e) full deletion | §8 deferred for re-evaluation after Phase 3 |
| d ≠ 5 generalization hook | §8 explicit tradeoff acknowledgment |
| Critic's vote for (c) over hybrid | §4 retains hybrid; rationale: D's value-only-consumer count is empirical, not cost-as-excuse |

### What was *not* absorbed in Round 2

- Critic argued "hybrids encode indecision" and recommended (c) clean.  Round 2 plan rejected this; Round 3 (below) accepted.
- Critic's "Option (e) delete record entirely": Round 2 plan adopted middle path; Round 3 (below) adopted full deletion.

### Round 3 — user sharpening (2026-05-22 evening)

After Round 2 plan committed, user observed:

> "걍 N_U같은 거창한 네임이 아니라 그냥 count-Lens at fractal
> level 2인거고 level Nat도 다 되는거자나?"
> ("It's not a grand name like N_U — it's just count-Lens at
> fractal level 2, and the level can be any Nat right?")

This reframing collapsed two earlier disputes:

1. **The name `N_U` is the import**.  Per CLAUDE.md
   "Universe-constant framing" failure mode catalog: "*Numerical
   readouts are Lens outputs; no quantity is a universe constant*".
   The `N_U` name *itself* is the violation; whatever it's
   defined as, the `def N_U` keeps the failure mode in scope.
2. **The 4-way convergence was fictional**.  fractalLens /
   coloringK25 / tensorDOF / injProjSpace are not 4 independent
   derivations of "5^25" — they are 4 verbal relabellings of ONE
   family value (`configCount 2`).  The record never had real
   content beyond decide-trivial identity.

### Round 3 absorbed into plan

- §2 Goal rewritten: canonical object is parametric family
  `configCount : Nat → Nat`; `N_U` demoted to `abbrev` (or deleted);
  `ResolutionInvariant` deleted entirely.
- §3 Phases restructured to 6 phases reflecting the sharpened goal.
- §4 explicitly retracts Round 2 hybrid; chooses clean Option (c) +
  Critic's Option (e).
- §6 Success criteria updated (0 `def N_U`, 0 `ResolutionInvariant`,
  0 `universe_level` def, plus `configCount` exists).
- §7 Out of scope strengthened (no `def N_U` restoration, no
  4-way record re-introduction).
- §8 Open questions trimmed (d generalization remains open;
  self-referential structural proof remains open).

### Self-check on Round 3

- §8.4 frame-import: the name `N_U` was the actual import; demoting
  it to `abbrev` (or inlining `configCount 2`) closes that channel
- Substrate metaphor: `configCount` is Lens *output*, parametric in
  level n — not a substrate
- Constructive accessibility: every phase has grep success criterion
  + Lean file deliverable
- Future-proofing: d generalization automatically open (parametric
  family extends naturally)
- Effort acknowledged: ~6-7 hr mean, 8-12 hr tail

The Round 3 sharpening shows that the *failure-mode catalog itself*
provided the diagnosis — the name `N_U` is *exactly* what CLAUDE.md
"Universe-constant framing" failure-mode warns against — and the
plan now treats the name as the import to be removed.  Earlier
rounds (synthesizer + critic) circled around this but didn't name
it; user (the framework originator) named it.

This plan should land before further N_U-using results are added.

### Self-check on this plan

- §8.4 frame-import check: §7 explicitly forbids promoting N_U; §5 docstring discipline risk added; no "this completes the picture" claims
- Substrate metaphor check: N_U as "count-Lens output", not "system substrate"
- Constructive accessibility: every phase has a concrete file deliverable + grep success criterion + effort estimate
- Open frontier honored: §8 has 5 genuine open questions including the framing (B) demotion + d≠5 generalization

This plan should land before further N_U-using results are added.

## §10 Registration

This plan is registered as next-session work in `HANDOFF.md` Part 2
"Open work" (or wherever HANDOFF tracks pending items).  Execution
not started; conversation closure pending.
