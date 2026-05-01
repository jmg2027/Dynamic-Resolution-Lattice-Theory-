# Session Handoff — 2026-05-XX (deep reorg + ready-to-merge audit)

## Branch

`claude/213-rust-engine-SloKB`, pushed to origin, working tree clean.
Last commit: `5926b73` (Phase 7 sync_namespaces SKIP update).

This session was **purely structural** — no new theorems, no new
observable predictions.  Architecture overhaul + audit infrastructure
+ documentation re-alignment.  All commits on the branch above; safe
to continue from here.

## TL;DR for next session

The repo has been deeply reorganized.  Run `python3 tools/layer_audit.py`
on session start — it will print the canonical layer distribution and
verify zero violations.  Then read `lean/E213/ARCHITECTURE.md` §0 (one
axis + Math/Physics topical) before doing structural work.

If you want to continue *theoretical* work (close another observable
to ppm/ppb precision, formalize a falsifier theorem, extend Real213
marathon), the structure is now stable and out of your way.

## What Was Done This Session

### 1. Layer-audit tool: mechanical layer derivation (★★★)

`tools/layer_audit.py` introduced.  Insight (Mingu): a file's layer
is not philosophical — it is mechanically determined by import
closure.  Rule: `layer(F) ≥ max(layer(I))` over all `E213.*` imports.

The script reports:
- **Violations** (path layer < natural layer): architectural
  inversions; must be 0.
- **Downgrade hints**: files at higher layer than mechanically
  required; informational, often intentional semantic placement.
- **Topical-cluster depth**: per-sub-folder (min, med, max) span,
  flagging WIDE (≥ 15) sub-folders as sub-clustering candidates.
- **Per-file vertical layer**: every file in Math/Physics gets
  classified into Kernel/Firmware/Hypervisor/Meta/App.

Final state: **0 violations across 907 files**.

### 2. Architectural framing correction: ONE axis (★★★)

Previous ARCHITECTURE.md spoke of "horizontal vs vertical axes" with
Math/Physics/Research as a separate axis.  That was wrong.

**Corrected**: there is only ONE axis (vertical: Kernel/Firmware/
Hypervisor/Meta/App).  Math/ and Physics/ are *topical labels*, not
layers — every file inside them lives at one of the vertical layers
mechanically determined by its import closure.

### 3. Deep reorg: Research/, Infinity/, Tactic/, Tools/ all retired (★★★)

The previous top-level dirs `Research/`, `Infinity/`, `Tactic/`,
`Tools/` are all gone.  ~370 files redistributed by content + import-
derived layer.  Lean tree now has *exactly* 7 top-level entries:
Kernel, Firmware, Hypervisor, Meta, App + Math, Physics (+ a few
umbrella .lean files: Math.lean, Physics.lean, Prelude.lean).

Distribution after reorg (per `layer_audit.py`):

| top-folder | Kernel | Firmware | Hypervisor | Meta | App | total |
|---|---|---|---|---|---|---|
| Kernel/      | 18 |   0 |   0 |  0 | 0 | 18  |
| Firmware/    |  0 |  25 |   0 |  0 | 0 | 25  |
| Hypervisor/  |  0 |   0 |  78 |  0 | 0 | 78  |
| Meta/        |  0 |   0 |   0 | 23 | 0 | 23  |
| App/         |  0 |   0 |   0 |  0 | 1 |  1  |
| Math/        | 36 | 211 | 231 |  6 | 0 | 484 |
| Physics/     |  2 | 168 | 105 |  0 | 0 | 275 |

Where Research/ went (337 files):
- **math content** → `Math/{Real213, CayleyDickson, Cauchy, ModArith,
  Modulus, Diagonal, Irrational, Hyper, Choice}/`
- **Lens framework research** → `Hypervisor/Lens/{Lattice, Compose,
  Properties, Morphism, Leaves, Refines, Kernel, Universal, Instances}/`
  + top-level `Initiality.lean`, `SemanticAtom.lean`
- **axiom-uniqueness metatheorems** → `Meta/{AxiomMinimality,
  AxiomMinimalityCapstone, Universal/{LensClaim, MorphismFactor,
  Reflection}}.lean`
- **Raw encoding research** → `Firmware/Raw/{DecEq, ComplexityClass,
  CmpIndependence, SwapSlashInjective}.lean`

Where the others went:
- `Infinity/` (9 files) → `Math/Infinity/`
- `Tactic/Omega213, QuadNorm` → `Kernel/Tactic/`
- `Tactic/{VerifyR4, DeriveR4Codomain}` → `Meta/Tactic/`
- `Tactic/{HurwitzRing, IntSquare, QuadExtension}` → `Math/Tactic/`
- `Tools/CertChecker.lean` → `Firmware/Tools/`

### 4. Hypervisor/Lens/ richly sub-clustered (★★)

Before: `Hypervisor/Lens.lean` (umbrella) + `Lens/{Instances,
Characterisation}/` (3 dirs).  After: 9 sub-clusters + 2 top-level
files:

```
Hypervisor/Lens.lean                  (Lens type definition, umbrella)
Hypervisor/Lens/
  Initiality.lean                     ← Raw initiality (was Research/)
  SemanticAtom.lean                   ← HasDistinguishing typeclass
  Characterisation/  (existing)
  Instances/         (5 → 25; merged Research/Instance/* + Lens/AB,
                      Cauchy, F9, Identity, NegSq, Prism, Swap, ...)
  Lattice/           (7) Join, JoinEquiv, Meet, Lattice, FamilyJoin,
                      FamilyMeet, IndexedJoin
  Compose/           (7) OnLens*, ImageMinimum, Factoring, Morphism
  Properties/        (10) ABRefines, CanonicalForm, EquivProperties,
                      IsLeaf, Leaf, ConstLensTotalKernel, ProdBelowId,
                      ParityCollapseFalse, InjectiveClass, TowerLevel3
  Morphism/          (7) BoolProp, BoolSqClassification,
                      DepthParityNotFold, Dist, FoldStructured,
                      NoDepthParity, SlashCharNotFold
  Leaves/            (5) DepthIncomparable, DepthJoin, Mod3, ModNat,
                      RefinesParity
  Refines/           (2) Chain, Preorder
  Kernel/            (8) CardinalityLB, Congruence, Corresp,
                      FourDistinct, FreeAudit, IdLensEq, Space,
                      SwapInvariant
  Universal/         (2) QuotLens, Flat
```

### 5. seed/AXIOM.md three-pillar uniqueness (★★)

`seed/AXIOM.md` now formalizes three-direction axiom uniqueness:

- **§1.1 (below)** — `Meta/AxiomMinimality{,Capstone}.lean`: removing
  any clause of Raw collapses the framework.  "Cannot weaken."
- **§1.2 (sideways)** — `Meta/UniversalLens/*` family: any
  distinguishing framework factors through Raw via injective Lens.
  "Everything else maps in."
- **§1.3 (above)** — `Firmware/Atomicity/{Five, PairForcing,
  NonDecomposable, Alive, ArityForcing[General], PrimitiveSizes}.lean`:
  given arity 2 + atomicity, `(NS, NT, d) = (3, 2, 5)` is THE shape.
  "Raw's own shape is forced."  *Pure-ℕ proofs that don't import Raw.*

Together: Raw is locked in three directions.

### 6. ready-to-merge skill created (★★)

`.claude/skills/ready-to-merge/SKILL.md` — comprehensive 9-phase
pre-merge audit that fuses every directional principle established
across ~10 sessions.

Phases:
0. Context absorption (HANDOFF, ARCHITECTURE, CLAUDE)
1. Mechanical layer audit (`tools/layer_audit.py` 0 violations)
2. Stale path / ref sweep
3. Build & purity (`rm -rf .lake/build && lake build` clean)
4. Doc cross-check (ARCH/CLAUDE/HANDOFF + seed/)
5. Catalog & narrative sync
6. Deprecated content deletion
7. `sync_namespaces.py` alignment
8. Commit hygiene
9. Verdict (READY TO MERGE or NOT READY + blockers)

Triggers: "ready to merge", "merge ready", "pre-merge",
"final audit", "ready audit".

### 7. ready-to-merge run: 4 additional fixes

Running the new skill on the post-reorg state surfaced 4 more drift
issues that were quietly there:

- `c4fb4b1` — `catalogs/math-theorems.md`: 105 lines `E213.Research.Real213.X` → `E213.Math.Real213.X`
- `c4e3573` — `seed/AXIOM.md` + `IMPLEMENTATION.md`: Research path refs (AxiomMinimality, SemanticAtom, CmpIndependence, Padic, Morphism/*) → current locations
- `5b07206` — `lean/E213/INDEX.md`: rewritten for post-reorg layout (was still describing Research/ + Tactic/ + Tools/ as separate top-levels)
- `5926b73` — `tools/sync_namespaces.py`: `DEFAULT_SKIP` updated for new Tactic/Infinity umbrella patterns + documented multi-namespace-file bug

Verdict: **READY TO MERGE**.

## Verification snapshot

```
$ python3 tools/layer_audit.py | head -8
# Layer audit — 907 .lean files under lean/E213/
Vertical: {'Kernel': 0, 'Firmware': 1, 'Hypervisor': 2, 'Meta': 3, 'App': 4}
Horizontal: ['Math', 'Physics']

## Violations: path layer < natural layer  (0)

$ cd lean && rm -rf .lake/build && lake build
Build completed successfully.

$ bash tools/kernel_regress.sh
✅ Kernel pure: 101 theorems verified 0-axiom.

$ python3 tools/sync_namespaces.py
scanned: 839 files, mismatches: 0
```

## Source-of-truth pointers (read these in order)

  1. `lean/E213/ARCHITECTURE.md` — canonical layer architecture.
     §0 = "one axis + topical labels".  §6.1 = mechanical-vs-semantic
     placement.  §6.2 = topical cluster sub-layering rule.
  2. `lean/E213/INDEX.md` — directory navigation, post-reorg.
  3. `STRICT_ZERO_AXIOM.md` (root) — strict-0-axiom theorem registry.
  4. `CAPSTONE_INDEX.md` (root) — top theorem map.
  5. `LESSONS_LEARNED.md` (root) — guardrails (finitism, rational-
     complex, Hunter L1-L5, etc.).
  6. `CLAUDE.md` — agent instructions + organizational philosophy.

## Where to find what (post-reorg)

| Question | Where to look |
|---|---|
| "What does DRLT compute?" | `Physics/Capstones/PureAtomicObservables.lean` + `CAPSTONE_INDEX.md` |
| "How does α_em derive?" | `Physics/AlphaEM/` chain (~18 files) |
| "Where is N_universe?" | `Physics/Foundations/NUniverseFractalDepth.lean` |
| "Why finite N only?" | `Math/Real213/DyadicTrajectory.lean` (limit ≠ exact) + `LESSONS_LEARNED.md` |
| "Atomic primitives?" | `Firmware/Atomicity/Five.lean` + `Firmware/Atomicity/PairForcing.lean` |
| "Kernel 0-axiom?" | `Kernel/` 18 files + `tools/kernel_regress.sh` |
| "Cohomology classes?" | `Math/Cohomology/` (~190 files in 10 sub-clusters) |
| "Lens framework?" | `Hypervisor/Lens.lean` + 9 sub-clusters under `Hypervisor/Lens/` |
| "Real analysis marathon?" | `Math/Real213/` (180 files) — was Research/Real213/ |
| "Cayley-Dickson tower?" | `Math/CayleyDickson/` (29 files) |
| "Universal Lens metatheory?" | `Meta/UniversalLens/` family (11 files) |
| "Axiom uniqueness (3 pillars)?" | `seed/AXIOM.md §1.1/§1.2/§1.3` + the linked Lean files |
| "Theoretical architecture?" | `lean/E213/ARCHITECTURE.md` (canonical) |
| "Pre-merge audit?" | invoke `ready-to-merge` skill |
| "Per-file mechanical layer?" | `python3 tools/layer_audit.py` |

## Current Precision Results (0 free parameters; unchanged this session)

| Observable | DRLT | Observed | Error |
|-----------|------|----------|-------|
| 1/α_em | 137.036 | 137.036 | **0.0004%** |
| m_p | 938.27 MeV | 938.27 MeV | 0.000% |
| m_μ/m_e | 206.7682837 | 206.7682838 | **0.48 ppb** |
| m_H | 125.28 GeV | 125.25 GeV | **+0.02%** |
| sin²θ₁₃ | 0.0220 | 0.0220 | **−0.07σ** |
| ν m₃/m₂ | 5.712 | 5.71 | **+0.04%** |
| η_B | 6.13×10⁻¹⁰ | 6.1×10⁻¹⁰ | 0.5% |
| Ω_Λ | 0.6850 | 0.685 | **0.0008%** |
| Magic numbers | 2,8,20,28,50,82,126 | (same) | **7/7 exact** |
| E_d (deuteron) | 2.271 MeV | 2.224 MeV | **+2.1%** |
| r₀ (nuclear radius) | 1.262 fm | 1.25 fm | **+0.95%** |
| a_V (volume) | 16.0 MeV | 15.5 MeV | **+3%** |
| a_S (surface) | 18.0 MeV | 16.8 MeV | **+7%** |
| a_C (Coulomb) | 0.685 MeV | 0.71 MeV | **−3.6%** |
| m_π (pion) | 137.6 MeV | 137.3 MeV | **+0.2%** |
| m_ω (omega) | 782.1 MeV | 782.7 MeV | **−0.07%** |
| m_J/ψ | 3081.6 MeV | 3096.9 MeV | **−0.5%** |
| Δ−N split | 295.7 MeV | 294 MeV | **+0.6%** |

(No new precision results this session — purely structural work.)

## Validation Standard #1+#2 closed (2026-05-01, unchanged)

`Physics/Capstones/ValidationStandardOne.validation_standard_capstone`
proves both:

**Standard #1 — precision** (4 observables share N_U = d^(d²) = 5²⁵):
  - `Physics/AlphaEM/MasterCapstone.alpha_em_master_capstone` —
    1/α_em(IR) at 0.18 ppb (≈ 500,000× tighter than 1/10⁴)
  - `Physics/Mass/MuOverEFinitist.mu_over_e_finitist` — m_μ/m_e at 0.49 ppb
  - `Physics/Cosmology/OmegaLambdaFinitist.omega_lambda_finitist` —
    Ω_Λ at 0.001 %
  - `Physics/Higgs/MassFinitist.higgs_mass_finitist` — m_H/v_H

**Standard #2 — measurable falsifiers** (closed Lean theorems):
  - `N_gen = 3` (no 4th generation)
  - 7/7 nuclear magic numbers atomic
  - `1/α_3 = NS² − 1 = 8` (color-confinement integer)
  - `hierarchy = d^(d²)/(d+1)` (no fine-tuning)

## Open Problems (priority order)

### 1. Source-level vs cached-olean discrepancy in IndexedJoin/FoldStructured

(★★ MOSTLY-RESOLVED — kept for context.)  Earlier in this session
`lake build E213.<...>.IndexedJoin` failed with `unknown identifier
'universalLens'` and `lake build E213.<...>.FoldStructured` similarly.
Both were *pre-existing* source breakage masked by olean cache.

The reorg incidentally cured them — sed-replace turned broken
partial-resolution `open E213.Research.X` lines into the correct
post-move paths.  Forced fresh rebuild (`rm -rf .lake/build &&
lake build`) is now clean.  But the lesson stands: **always force-clean
build before claiming done.**  The skill encodes this in Phase 3.

### 2. sync_namespaces.py multi-namespace bug

`Math/Infinity/Countable.lean` declares two namespaces in one file:
`namespace E213.Firmware.Internal` (helper access) followed by
`namespace E213.Infinity` (own content).  The tool's `first_namespace`
returns only the first match.  When applied, this generates a
spurious `(E213.Firmware.Internal, E213.Math.Infinity.Countable)`
rename pair, then global-rewrites that EVERYWHERE — corrupting every
legitimate use of `E213.Firmware.Internal` (Cmp/Levels/Slash/Swap/...).

**Short-term fix applied** (`5926b73`): added `lean/E213/Math/Infinity`
to `DEFAULT_SKIP`.

**Long-term fix needed**: detect multi-namespace files, emit one
rename pair per namespace, OR refuse to auto-align such files.  Fix
in `tools/sync_namespaces.py:apply_global_renames()`.

### 3. WIDE topical sub-clusters (informational)

`tools/layer_audit.py` reports two WIDE-span sub-folders (depth ≥ 15
chain within cluster):

- `Math/Cohomology/` — 195 files, depth span 44.  Single mega-folder.
  Should be sub-clustered by depth band (foundations / mid /
  capstones).  Existing sub-clusters help but the overall span is
  still large.
- `Math/Real213/` — 180 files, depth span 90 (essentially a flat
  marathon chain).  Sub-clustering by depth band would replace
  current `PhaseAC, PhaseAD, ..., PhaseLCapstone` session-numbered
  names with content-driven groupings.

Not blockers; informational.  Per `ARCHITECTURE.md §6.2`, action when
the span makes navigation actively harder.

### 4. 19 downgrade hints (informational, intentional)

`tools/layer_audit.py` reports 19 files at higher path layer than
mechanically required.  All are intentional semantic placements per
`ARCHITECTURE.md §6.1`:

  - `Firmware/Atomicity/{Five, PairForcing, NonDecomposable, Alive,
    ArityForcing[General], PrimitiveSizes}` — pure-ℕ at Kernel
    mechanically; kept at Firmware as Raw's forced-shape obligation.
  - `Hypervisor/Lens.lean` — Firmware-level imports; kept as
    Hypervisor umbrella.
  - `App/Simplex.lean` — Firmware-level mechanically; kept at App
    as 213's application.
  - 5 files in `Meta/` — meta-level claims whose proofs don't need
    Meta machinery; kept at Meta because the claim is metatheoretic.

No action.  Informational only.

### 5. Theory-side capstones still pending (carry-over)

- **Λ_QCD finitist closure** (m_p, η_B, ν chain to N_U).
- **Lens cardinality at fractal level d²** — full Lean derivation.
- **More Pisano primes** (mod 97, 101, 103 — bigger periods).
- **Tribonacci CRT extension** (mod 11, 13).
- **Self-bootstrapping Kernel.Proof** — eliminate propext +
  Quot.sound from non-Kernel layers via deep-embedded proof system.

## Unresolved from this session

This session closed everything it set out to do.  No dead ends.

One self-correction trajectory worth noting for posterity: I twice
made misclaims about deletions ("notes/ deleted" when it was actually
renamed to `research-notes/`; "AUDIT_Lean.md deleted" when it
exists).  Both were caught + corrected within the same session.
The `ready-to-merge` skill Phase 4 codifies "verify deletion claims
with `find` / `git log` before propagating" to prevent recurrence.

## Tooling reference (where things live now)

  - `tools/layer_audit.py` — derive each file's natural vertical
    layer from import closure.  ★ NEW this session.  Run on every
    structural change.
  - `tools/sync_namespaces.py` — auto namespace↔path alignment
    (sentinel-protected single pass).  Workflow: `git mv` + `python3
    tools/sync_namespaces.py --apply --include-rust`.  Known bug
    with multi-namespace files (see Open Problem #2).
  - `tools/kernel_regress.sh` — verify Kernel/ stays 0-axiom (101 thms).
  - `tools/audit_axioms.py` — full-tree axiom survey.
  - `tools/port_candidates.py` — find unported Lean→Rust mirror.
  - `rust-engine/tools/lean-rust-diff` — Lean ↔ Rust BigUint
    differential equivalence (43/43 OK).

## Available skills (`.claude/skills/`)

  - `ready-to-merge` ★ NEW — comprehensive 9-phase pre-merge audit
  - `verify-consistency` — narrower scope (numerical/notational)
  - `purity-check` — 0-sorry / 0-axiom verification
  - `lake-build-verify` — quick build sanity check
  - `doc-sync` — doc updates after structural moves
  - `catalog-sync` — sync catalogs/ after Lean theorem additions
  - `handoff` — generate this file
  - `marathon-start` — kick off a new blueprint marathon
  - `integrate` — branch integration

## Recent commits (this session)

```
5926b73  Phase 7 sync_namespaces: DEFAULT_SKIP for post-reorg layout
5b07206  Phase 6 cleanup: lean/E213/INDEX.md updated for post-reorg layout
c4e3573  Phase 4 cross-check: seed/ Research paths → current locations
c4fb4b1  Phase 2 sweep: catalogs/math-theorems.md Research → Math (105)
27f8370  Add ready-to-merge skill: comprehensive pre-merge audit
bf34de0  Drop Research/ marker dir entirely: distribute by topic
0913a6e  Reorg final: docs (ARCHITECTURE/HANDOFF/CLAUDE) reflect new layout
089f722  Reorg cleanup: layer violations 18 → 0
733447a  Reorg Groups 7+8: Tactic/ and Tools/ distributed by layer
355a23d  Reorg Group 6: Infinity/ → Math/Infinity/
183b29d  Reorg Group 5: distribute remaining Research/* loose files
0a4fca2  Reorg Group 4: Raw research → Firmware/Raw/Research/
9afea67  Reorg Group 3: Meta-related Research/ → Meta/
5db8924  Reorg Group 2: Lens-related Research/ → Hypervisor/Lens/Research/
117445f  Reorg Group 1: math-flavored Research/ → Math/
bb5a5cb  Correct architectural framing: every file has a vertical layer
4bed5d3  layer_audit.py: extend with horizontal cluster depth analysis
94197f4  tools/layer_audit.py: import-graph-derived layer audit
```

Cumulative scope: ~643 files changed, 4396 insertions, 4552 deletions.

## Architectural principles (now codified)

These were absorbed across ~10 sessions and are now first-class
operational rules.  When in doubt, default to these:

  1. **One vertical axis** — Kernel ↑ Firmware ↑ Hypervisor ↑ Meta ↑ App.
  2. **Math/ + Physics/ are the only horizontal labels.**  Not layers.
  3. **`tools/layer_audit.py` is the truth.**  If it reports
     violations, those are real architectural inversions; fix them.
     If it reports downgrade hints, those are intentional unless
     proven otherwise.
  4. **Path = namespace, ideally.**  Intentional exceptions
     (Tactic short-form, Math/Infinity umbrella, Firmware/Raw
     internal helpers) live in `tools/sync_namespaces.py:DEFAULT_SKIP`
     and are documented in ARCHITECTURE.md.
  5. **Sub-cluster early** (≥3 thematically-related files).  Don't
     merge files just to reduce count.  Three similar lines is better
     than a premature abstraction.
  6. **Delete deprecated content with no active dependents** — but
     preserve a README marker pointing to the recovery commit.
  7. **0 sorry, 0 axiom (≤ {propext, Quot.sound})**, no Mathlib,
     no Classical, no native_decide.
  8. **Three-pillar uniqueness** (AXIOM.md §1.1/§1.2/§1.3): minimality
     below, universality sideways, forced-shape above.
  9. **Self-correct on misclaims.**  If a previous claim said "X was
     deleted" but X exists, fix the claim first.  Don't propagate
     wrong claims by editing files to match.
 10. **`rm -rf .lake/build && lake build`** before claiming a build
     is clean.  Cached olean hides source-level breakage.

## Suggested next-session entry points

Pick one based on what's most interesting:

### A. Theory: close another observable to ppm/ppb

Use `Math/Real213/` real-analysis machinery + `Physics/Capstones/`
template to formalize a new precision claim.  Candidates:
  - **Λ_QCD** (currently approximate; full closure would unlock
    proton mass + η_B + ν chain to N_U)
  - **m_n/m_p ratio** (1 ppb level closure mentioned in
    `LESSONS_LEARNED.md`)
  - **g_p magnetic moment** (0.097 ppm closure mentioned)

Each ends with a strict `does not depend on any axioms` capstone in
`Physics/Capstones/`.

### B. Theory: formalize a new falsifier

Standard #2 expansion.  Candidates from `seed/FALSIFIABILITY.md`:
14 measurement propositions.  Most are unformalized.  Pick one and
close it as a Lean theorem `< validation_standard_capstone` style.

### C. Real213 marathon continuation

`Math/Real213/` has 180 files in a deep chain (depth span 90).
The chain closes various calculus / analysis theorems.  Look at
`PhaseDKUltimate.lean` (current head of the chain) and continue
adding lemmas.

### D. Tool work: fix sync_namespaces multi-namespace bug

See Open Problem #2.  Self-contained, ~50 LoC change.  Adds robust
support for files like `Math/Infinity/Countable.lean`.

### E. Sub-clustering: depth-band split of Math/Cohomology or
    Math/Real213

See Open Problem #3.  Use `tools/layer_audit.py` topical-cluster
depth report to identify natural sub-bands.  Reorganize within the
same vertical layer (no namespace/import semantic changes).

### F. New marathon (blueprint-driven)

`blueprints/{math,physics,meta}/*.md` lists planned formalization
campaigns.  Use the `marathon-start` skill to kick one off.

## Self-test on next session start

1. Read this HANDOFF.md (you're doing it now).
2. Run `python3 tools/layer_audit.py | head -8` — confirm 0 violations.
3. Run `cd lean && lake build` — confirm clean (cached is fine).
4. Read `lean/E213/ARCHITECTURE.md §0` for the architectural
   framing.
5. Pick an entry point from the list above OR ask Mingu what's next.

## Authors

  - Mingu Jeong (Independent Researcher) — theory.
  - Claude (Anthropic) — formalization assistance, code,
    architectural audit.
