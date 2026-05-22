# G120 — N_U re-derivation plan

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

## §2 Goal (target state)

After execution:

1. `N_U` has **one** definition in `Lib/Math/ResolutionLimit.lean`.
   `UniverseChain.Universe.N_U` and `NResolutionFromFractal.n_resolution_candidate`
   become `theorem`s (not `def`s) that reduce to it.
2. Each spec-sanctioned framing that has a real derivation is wired
   into `ResolutionInvariant` as a *theorem field*, not a placeholder.
3. Framings without a derivation are either deleted from the record
   or replaced with an honest `Prop`-level marker, not a bare `:= N_U`.
4. `numV` name collision resolved by namespace separation.
5. ValidationStandard decide-chain unchanged.  Literal value
   `298023223876953125` preserved at consumer sites.

## §3 Phases

### Phase 1 — Canonicalize the definition (small)

- **Scope**: collapse three defs into one.
- **Files changed**:
  - `Lib/Math/UniverseChain/Universe.lean`: replace `def N_U : Nat := 5^25`
    with `theorem N_U_eq : Universe.N_U = ResolutionLimit.N_U := by decide`,
    or rewrite the structure field to reference `ResolutionLimit.N_U`
    directly.
  - `Lib/Physics/Foundations/NResolutionFromFractal.lean`: keep
    `n_resolution_candidate` as a *local* convenience def with a
    `theorem n_resolution_candidate_eq_N_U` bridge.
- **Success**: `grep -rn "def N_U" lean/E213/` returns exactly one hit.
- **Effort**: 30 min.
- **Depends on**: nothing.

### Phase 2 — Wire real derivations into `ResolutionInvariant` (medium)

- **Scope**: replace the rfl-placeholders for `fractalLens` and
  `coloringK25` with the existing external theorems.
- **Files changed**:
  - `Lib/Math/ResolutionLimit.lean`: change `ResolutionInvariant`
    fields from `Nat := N_U` to `: (… = N_U)`-shaped propositions, OR
    keep numeric fields but add a sibling `ResolutionInvariantProofs`
    record holding the four equality theorems.
  - Import `NResolutionFromFractal.n_resolution_eq_hierarchy` and
    `FractalLensCardinality.K25_coloring_count_eq_N_U`.
- **Success**: `#print axioms` clean on the new record; old
  placeholders gone; consumers still compile.
- **Effort**: 2-3 hr.
- **Depends on**: Phase 1.

### Phase 3 — Honest treatment of stub framings (small)

- **Scope**: tensor (#3) and injProj (#4).
- **Decision**:
  - `tensorDOF`: **DELETE** from `ResolutionInvariant`.  Re-add only
    if/when a real Tensor type with a rank predicate exists.  Until
    then it is docstring fiction.
  - `injProjSpace`: **DO NOT ADD**.  Spec §2.4 informal; no witness;
    keep out of the Lean record.
- **Files changed**: `Lib/Math/ResolutionLimit.lean` (remove two
  fields), `STRICT_ZERO_AXIOM.md` (update categorization).
- **Success**: every field of `ResolutionInvariant` has a real
  external derivation cited in its docstring.
- **Effort**: 30 min.
- **Depends on**: Phase 2.

### Phase 4 — Resolve `numV` collision (small)

- **Scope**: rename one of the two `numV` definitions.
- **Decision**: rename `Fractal/Level.lean`'s parametric version to
  `vertexCountAtLevel (L : Nat) : Nat := 5^L`.  Keep `V25.lean`'s
  `numV : Nat := 25` as the concrete instance.  Add
  `theorem numV_eq_vertexCountAtLevel_two : numV = vertexCountAtLevel 2`.
- **Files changed**: `Fractal/Level.lean` and any callers.
- **Success**: `grep -rn "def numV" lean/E213/` returns exactly one hit.
- **Effort**: 1 hr.
- **Depends on**: nothing (parallel to Phases 1-3).

### Phase 5 — Audit + commit

- `lake build` clean, `tools/scan_axioms.py` PURE on every touched
  module, decide-chain in ValidationStandard capstones still resolves.
- **Effort**: 30 min.

## §4 Resolution of A-vs-D divergence

**Reject Option (b)** (split constants per framing): produces four
disconnected numerals, severs the decide-chain D identified, no
spec-§8 benefit since the framings already share a single numeric
target — splitting the *definition* doesn't change the fact that the
*number* is one.

**Adopt Option (a) augmented with Phase 3 of Option (c/d)**: single
canonical `N_U` definition (D's recommendation), but `ResolutionInvariant`
is purged of placeholder fields and only carries framings with real
derivations (C's concern about cosmetic identity).

- **Neutralizing D's concern** (capstone cascade): Phase 1 preserves
  the literal value and the `decide` chain.  ValidationStandard
  consumers are untouched.  Cost: 30 min, not 1-2 days.
- **Neutralizing C's concern** (universe-constant smell): Phase 3
  deletes the two fields that exist only to *look* like a universe
  invariant.  The record stops claiming "four observables share one
  invariant" via placeholders; it claims "two derivations land on the
  same numeral" via theorems.  No framing (B) self-reference promotion;
  no §8 violation.

This is a hybrid leaning toward (a), with the §8-hygiene step from (c)
applied surgically rather than as a full migration.

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

## §6 Success criteria (objective)

1. `grep -rn "^def N_U" lean/E213/` returns exactly one line.
2. `grep -rn "^def numV" lean/E213/` returns exactly one line.
3. Every field of `ResolutionInvariant` has form `: <expr> = N_U` with
   a proof referencing an external theorem (not `rfl` on a placeholder).
4. `cd lean && lake build` clean.
5. `python tools/scan_axioms.py E213.Lib.Math.ResolutionLimit` reports
   PURE on every theorem touched.
6. ValidationStandard capstones
   (`ValidationStandardOne`, `FinitistObservableChain`,
   `PureAtomicObservables`, `AlphaEM.Capstone`) build unchanged.
7. `#print axioms` on the new theorem fields → "does not depend on any
   axioms".

## §7 Out of scope

- Promoting `N_U` to a privileged status, or renaming
  `ResolutionInvariant`.  The record stays a numerical agreement
  artifact, not a universe-constant claim.
- Adding tensor or injProj derivations.  If they emerge later they
  re-enter via a new file, not by un-deleting placeholder fields.
- Framing (B) self-reference formalization.
- Restructuring `PureAtomicObservables` orientation ("no N_U
  dependence" branding).  Orthogonal concern; address in a separate
  note if it becomes problematic.
- Touching `catalogs/constants.md` numerics.

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
- **Generalization hook**: if d ≠ 5 questions surface (or fractal
  level ≠ 2 generalizations), is `numV` / N_U structure parametric
  enough to extend, or does `5^25` baked at consumer sites prevent
  generalization?  Currently consumer literals are hardcoded; this
  is a present-vs-future-research tradeoff.  Plan does not refactor
  to parametric form, but flags this as the next generalization gate.
- **Option (e) deferred**: critic surfaced "delete `ResolutionInvariant`
  entirely".  Only 2 of 4 framings are real (fractalLens, coloringK25);
  the record may be conjectural overreach.  Plan adopts middle path
  (delete 2 placeholder fields, keep 2 proven ones) but a future
  promotion or further audit may opt for full deletion.  Re-evaluate
  after Phase 3 lands.

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

### What was *not* absorbed

- Critic argued "hybrids encode indecision" and recommended (c) clean.  Plan rejected this: D's risk audit is empirical (25 value-only consumers + ValidationStandard cascade), not a §8.4-disguised cost argument.  Cost reflects real downstream load, which matters for whether the plan can execute without breaking the precision chain that DRLT Validation Standard #1 depends on.
- Critic's "Option (e) delete record entirely": plan adopts middle path (delete 2 placeholders, keep 2 proven), with full deletion as deferred open question.  Rationale: 2 proven framings (fractalLens, coloringK25) are real derivations and deserve a slot somewhere; if not in `ResolutionInvariant`, they need a new home — that's more cost than the placeholder removal.

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
