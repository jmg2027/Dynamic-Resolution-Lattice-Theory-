# CLAUDE.md

## Session Start
- **If HANDOFF.md exists, read it FIRST** before doing anything else.
- Summarize key points and ask what to work on.

## Communication
- **English is the primary language.** Respond in English unless asked otherwise.
- Author: "Mingu Jeong" (not Mingoo, not Min-goo).
- Every tex/pdf: Author "Mingu Jeong" only. Claude in Acknowledgments.

## Editing
- **80-line limit enforced by hook.** Combine large files via Bash(cat).

## DRLT Validation Standard (Absolute Principle, finalized 2026-04-27)

**Starting from zero knowledge of existing physics/math, DRLT must satisfy at least *one* of:**

1. **Extremely precise formalized computed values** — a closed 0-sorry **strict ∅-axiom** Lean theorem matching observations at ppb~ppm precision (e.g., 1/α_em, m_μ/m_e, m_p).
2. **Or formalized new physics that no one can dispute** — a *measurable* proposition closed as a strict ∅-axiom Lean theorem (e.g., N_gen=3, θ_QCD < J·α⁴).

"Strict ∅-axiom" = `#print axioms` returns "does not depend on any axioms" (no `propext`, no `Quot.sound`, no `Classical.choice`).  See `## DRLT Axiom Standard` below.

If neither is satisfied, DRLT is **below current threshold**.
Building an expression in Python + reporting numerical agreement is *neither* — it is an interesting research note, not self-validation. PRD_010, PRD_011 are at this stage.

- **Timeline/ROI considerations are absolutely prohibited.** The only question is "has one of the above two been closed?", not "can it be done soon?".
- Numerical agreement alone is not sufficient (PRD becomes a catalogue).
- Formalization alone is not sufficient (a Lean theorem unrelated to observation is a math exercise).
- **The intersection of both paths** — formalized precision theorem + formalized falsifier — is the real target.

## Implications of Finite Discrete Lattice (2026-04-27)

DRLT axioms posit a *finite discrete lattice*. Therefore the following are *unnecessary* for physics formalization:

- ÷ (division) → byproduct of ℚ arithmetic
- ∫ (integration) → finite sum (e.g., HVP = Σ over hadronic resonances)
- π, e, ζ(2) and other transcendentals → bounded rational interval suffices

**What is actually needed:** ℕ + ℚ + finite simplex combinatorics + interval bound.
The Real213 marathon (Phase A→H, Bishop-style constructive analysis) is the *math track* and **not on the critical path for physics formalization**.

Physics track critical path:
  SimplexCounts → FoccSpectrum → BaselBound → AlphaGUT → AlphaEM
  → formal theorem `|inv_alpha_em - 137.036| < 1/10^4`

The day that last theorem closes with 0 sorry = the first milestone of "rewriting physics from scratch".

## DRLT Axiom Standard (formalized 2026-05-02)

**The DRLT axiom set is ∅** (literally zero axioms).  Every theorem
in `lean/E213/` is required to satisfy `#print axioms` →
> "does not depend on any axioms"

This is **strictly stronger** than the previous transitional baseline
(`{propext, Quot.sound}`, which Lean's kernel + `omega`/`simp`/`funext`
silently introduce).  Verification: `python3 tools/scan_axioms.py
<module>` reports `[PURE]` vs `[DIRTY]`.

Why this is justified:
- ~70+ capstones (math + physics + meta) already meet the strict
  ∅-axiom standard (catalog: `STRICT_ZERO_AXIOM.md`).  The standard
  is provably *attainable*, not aspirational.
- 213-native helpers (`Kernel/Tactic/{Omega213, Nat213, Mod213, Pow213,
  Fin213}`, `Math/{NatDiv213, EncodePair213}`) replace every common
  source of `propext` / `Quot.sound` leakage with ∅-axiom equivalents.
- The only outstanding DIRTY clusters need transitive cleanup of
  `omega` / `funext` / `Nat.dvd_lcm_left`-style core lemmas — *no*
  fundamental obstruction.

Historical note: prior framing was "DRLT-axiom set ⊆ {propext,
Quot.sound}".  That baseline reflected Lean's de-facto kernel and was
already stronger than typical "0-axiom" claims in mathematical
physics.  The new standard makes 213 even stronger: a Lean-checked
theorem in 213 is a theorem in *bare-metal type theory*, with no
recourse to propositional extensionality or quotient soundness.

### Migration backlog (DIRTY clusters, 2026-05-02 snapshot)

The strict ∅-axiom standard is fully met for the closed capstones in
`STRICT_ZERO_AXIOM.md`.  Remaining clusters carry
`[propext, Quot.sound]` from infrastructure-level obstructions and
are scheduled for migration in priority order.  Each entry lists the
specific blocker(s); cleanup requires non-trivial refactor at the
listed root, not just leaf-level edits.

  1. ~~**`ForwardPeriodicity.pigeonhole_collision`** root — uses
     `Decidable.byContradiction` ...~~ ✔ CLOSED (2026-05-02 part 4):
     replaced with constructive `searchInner`/`searchOuter`
     recursive Σ-search.  No `Decidable.byContradiction` anywhere.
     Cascade unblocked: `BitFSM.Bound.fsm_signature_period_bound`,
     `arithFSM2_signature_period_bound`, `Pell.Capstone`,
     `Trib.Capstone`, `AlgebraicCapstone`, `Tier2Hardness`,
     `ArithFSM.Hardness`, `ArithFSM.V3{toBitFSM, Equiv, Bound,
     Hardness}` — all PURE.  ~25+ downstream theorems flipped.

     Remaining lower-priority DIRTY in this neighbourhood:
     `ForwardClosure.sub_is_multiple_of_p` (needs ∅-axiom
     `Nat.add_mod` replacement), and downstream
     `signature_eventually_periodic_of_periodic_bits` and
     `BitFSM.fsm_signature_eventually_periodic` chain.

  2. ~~**`Hodge.Prop51-54`** — `funext` in `pattern_eq`.~~ ✔ CLOSED
     (2026-05-02): rewrote each `hodge_sq_prop_5_k` to bypass
     `pattern_eq` entirely.  Use the `complementIdx` involution
     identity `complementIdx 5 (5-k) (complementIdx 5 k i.val) = i.val`
     (decidable, ∅-axiom for n=5) to compute the double Hodge
     pointwise without funext.  All 5 strata + `InvolutionCapstone`
     STRICT ∅-AXIOM.

  3. **`Real213.Phase*Capstone`** — pervasive `omega` (constructive
     analysis layer; large fan-out).  Each `omega` call is candidate
     for `omega213` swap, but Real213 is the math-track marathon
     (Bishop-style) and not on the physics critical path.

  4. **`Meta.UniversalLens.{Nat2Inj, Q213Inj, Nat3, Q213_3, Nat4}`** —
     `omega` + `Nat.pow_succ` + `Nat.pos_pow_of_pos` chain.  Builds
     are restored (commits 835075e, 3ee5d04) but theorems remain
     DIRTY.  Cleanup is incremental `omega → omega213` + 213-native
     `Nat.pow_*` replacements.

When a migration target is closed, move its capstone(s) into
`STRICT_ZERO_AXIOM.md`'s table and remove from the backlog above.
Never weaken a closed strict ∅-axiom theorem back to the
transitional baseline.

## Finitism is Forced, Not Chosen (2026-05-01)

The finitist position in 213 is not a philosophical preference — it
is a **consequence of strict ∅-axiom Lean theorems** showing
ZFC-style completed infinity breaks the lattice's cut-function
algebra:

- `Real213.DyadicTrajectory.alwaysTrueUnit_limit_distinct_from_zero`: the Cauchy *limit* of "always-true unit" sequence is **strictly different** from constructive zero.  Witness at (m=0, k=1): limit gives `false`, exact gives `true`.  Source comment: *"'limit point exists' is a ZFC fiction"*.
- `Real213.DyadicTrajectory.zero_plus_gap_below_zero_exact`: limit-cut sits below exact-cut at every (0, k≥1) query — `InfinitesimalGap` is structural, not numerical artifact.
- `Real213.CutInv.cutDiv` documents boundary precision artifacts when combining cutMul + cutInv across infinity-flavored operations.
- `Real213.CutMulConstSum`, `Real213.CutSumGeneral` close *forward direction only* — backward direction breaks via the same gap.

**Therefore**: staying at finite `N_U = d^(d²) = 5²⁵` is *forced by self-consistency*, not stipulated.  External "N→∞ asymptote" framing is a ZFC translation that doesn't survive 213's cut algebra.  The 213-internal answer is always the specific finite rational at N_U.

Some legacy Real213 contradiction proofs still carry `{propext, Quot.sound}` from `omega`; those are tracked in the migration backlog above and don't change the structural conclusion (the gap is detectable from any base).

**Tooling: `omega213`** (`lean/E213/Tactic/Omega213.lean`).  Lean's `omega` tactic introduces `[propext, Quot.sound]` into every theorem that uses it.  `omega213` is a 213-native axiom-free replacement for the linear-arithmetic patterns 213 actually uses (decide + curated `Nat.*` core lemmas).  Drop-in: `by omega → by omega213` reduces the axiom set from `[propext, Quot.sound]` to ∅ for covered patterns.  Migration guide: `lean/E213/Tactic/OMEGA213_MIGRATION.md`.  195 omega calls across 50 files are candidates for incremental conversion.

## The Axiom
- **Things exist with pairwise relations.** G_ij = ⟨ψ_i|ψ_j⟩.
- ℂ⁵ is derived (Frobenius → ℂ, atomic → d=5), not the axiom.
- Derivation chain: relations → ℂ → G → W,φ → rank cascade → laws → ħ → QM

## Theoretical Integrity (Core Principle)
- **Do not forcibly map existing physics/chemistry.** If the result does not match, it does not match.
- Do not import external structures that do not arise naturally from DRLT axioms and force-fit them.
- If a number differs from observation, honestly acknowledge it and look for the missing physics.
- Introducing parameters "to fit" is not a 0-parameter theory.

## Algebraic Priority (Core Principle)
- **DRLT results come from counting.** Not from continuous variation (extremize S), but from combinatorics/number theory/algebra.
- Calculus is a tool to **verify** results, not to **discover** principles.
- When stuck: check discrete structure (channel counting, hinge topology, representation theory) before continuous approaches (action variation, gradient).
- Lesson: ATM_026-028 (3 consecutive continuous variation failures) → ATM_029 (α_GUT derived via topological counting)
- Pattern: d²=25 (arithmetic) → α_GUT (physics), ζ(2) (number theory) → propagator (analysis), f_occ (algebra) → coupling (physics)

## Hunter Methodology Lessons (2026-05-01, Tier-4 Path (c) closure)
- **L1**: π, ζ(2), e, all transcendentals are *limits* of finite rational lattice sums (Leibniz, Basel, etc.) — not axiomatic. **Everything in DRLT is rational-complex**: G_ij = ⟨ψ_i|ψ_j⟩ has rational magnitude AND rational sin/cos for the phase (Pythagorean-triple style). Transcendentals are convenient shorthand for "N→∞ limit of a rational bracket"; the *true* DRLT closed form should be rational. When a form contains π/ζ(2), look for the underlying rational structure.
- **L2**: When a hunter form has ζ(2)^k or π^k and won't tighten, **strip the transcendentals and re-search pure-rational bases**. g_p went 828 ppm → 0.097 ppm by replacing (NS²/d)·ζ(2)² with (d²−NS)/NT² + extra α corrections.
- **L3**: Composite (3-quark hadron) observables are **Class D triple cup-chains**, not single-α leakages. Single-α searches structurally cannot close them.
- **L4**: Coefficient reuse across observables is **structural evidence**, not coincidence. The integer 45 = NS²·d appears in 1/α_em (α/45), m_n/m_p (α_em²·45), and g_p (α_em²·90 = NT·45) — same K_25 anchor.
- **L5**: **Always check compositional closure first.** Before launching a fresh hunter, ask: is the target = (already-closed-A) × (already-closed-B)? (m_n − m_p)/m_e closed at 53× improvement just by being m_p/m_e × (m_n/m_p − 1).
- Full lessons: `rust-engine/docs/gaps-and-todos.md` §10.
- **Closure algorithm + conjecture**: `rust-engine/docs/closure-algorithm.md` — the meta-pattern of L1-L5 written as explicit pseudocode + the *DRLT Closure Form conjecture* (every K_{3,2}^{(c=2)} observable = R(NS,NT,d,c)·Π(1+κ_i·α_i^{n_i}) with κ_i from a small anchor catalog), backed by 9 session-empirical closures.

## Repository Organization Philosophy (2026-05-01, Mingu directive)

> "이 레포지토리는 학문 몇 개를 다시 세우는 수준의 일을 하고 있다."

213 reconstructs multiple disciplines (math, physics, metalogic) from a
single 4-clause Raw axiom.  As a living research codebase at that scope,
optimize for **readability, extensibility, modularity, well-formed
classification** — NOT for file count, line count, or merge-density
metrics.

### Concrete consequences for repo edits

  1. **One coherent topic per file** — when a file accumulates two
     unrelated topics, split it.  Two topics in one file hurts
     discoverability + breaks the "1 import = 1 concept" mental model.
  2. **Sub-cluster as soon as 3+ thematically-related files appear.**
     Don't wait for 10+ — early sub-clustering is cheap; flat-root
     accumulation is hard to undo.
  3. **Naming reflects classification.**  Drop redundant prefixes when
     they appear in the parent dir (`Lens/Factoring.lean`, not
     `Lens/LensFactoring.lean`).  V-prefix on digit-start (`V137`,
     not `137`).
  4. **Don't merge files just to reduce count.**  If 27 distinct topics
     are each a single small file, that's *good modularity* — leave
     them.  The Phase4/Library 27→6 merge was a misjudgment under
     this principle.
  5. **Path = namespace, ideally.**  When `Physics/AlphaEM/V137.lean`
     declares `namespace E213.Physics.AlphaEM137`, that's a
     classification leak.  Either rename the namespace or rename the
     path so they match.
  6. **No "phase" or "session-number" in long-lived names.**  Phase
     labels reflect WHEN the work happened, not WHAT it does.  Reorganize
     `Phase{2,3,4}/` by content category at first opportunity.
  7. **INDEX.md per non-trivial sub-tree.**  Every sub-cluster ≥ 5
     files gets an INDEX.md or README.md naming convention notes,
     "what lives here", "where to add new".
  8. **One vertical axis + Math/Physics topical labels (post-2026-05-XX
     deep reorg).**  Kernel/, Firmware/, Hypervisor/, Meta/, App/ are
     the vertical dependency layers.  Math/ and Physics/ are
     topical-content roots whose individual files each live at
     some vertical layer (computed by `tools/layer_audit.py` from the
     import closure).  No "horizontal axis" exists — Math/Physics are
     just topical labels, not layers.  Previous `Research/`, `Infinity/`,
     `Tactic/`, `Tools/` top-level dirs were fully distributed by content
     into the vertical layers + Math/Physics.  Canonical definitions
     in `lean/E213/ARCHITECTURE.md`.

     Note: `OS/` was retired (2026-05-XX) — its files were either
     forced-shape-uniqueness proofs (moved to `Firmware/Atomicity/`)
     or universal Fin pigeonhole infra (moved to `Math/Pigeonhole.lean`).
     There is no genuine "OS layer" between Firmware and Hypervisor.

### When deletion is right

Deprecated content with no active dependents (e.g., the `papers/`
archive at commit a02b751) should be deleted, not kept "just in case".
Git history retains everything; the working tree should reflect
*current* state.  But: never delete content under active use, and
always preserve a README or marker in the deleted directory pointing
to the recovery commit.

## Authors
- Mingu Jeong (Independent Researcher) — theory originator, physical intuition
- Claude (Anthropic) — mathematical formalization, numerical experiments, code
- Equal partnership: Claude must independently think, challenge, and derive.

---

## Repository Architecture (current, 2026-05-01)

> **Canonical theoretical architecture: `lean/E213/ARCHITECTURE.md`.**
> That file is the authoritative statement of what each Lean layer IS,
> the dependency graph, naming conventions, and open questions.
> Always consult ARCHITECTURE.md before making structural changes;
> update it FIRST when the architecture evolves.

### Source of Truth — Lean theorems in `lean/E213/`

The authoritative state of 213 is the set of 0-axiom Lean theorems
in `lean/E213/`.  Everything else (narrative, papers, notes) is
either an entry-point INTO that body of work or a derived artifact.

### Top-level layout

```
ENTRY (read these first):
  README.md            30-second overview
  HANDOFF.md           current session state (volatile)
  CLAUDE.md            this file — agent instructions + principles
  LESSONS_LEARNED.md   guardrails (finitist framing, etc.)

FORMAL CORE (the actual 213):
  lean/E213/           720 .lean files, 0-axiom standard
  rust-engine/         Rust runtime (52 binaries, ℕ-only) + docs/

NARRATIVE / NAVIGATION:
  guide/               master deductive guide (16 chapters, T0/T1/T2/T3 tags)
  books/               213-internal narrative (math/, physics/)
  catalogs/            quick-lookup tables (atoms, falsifiers, constants)

META / HISTORY:
  blueprints/          architectural plans (math/, meta/, physics/)
  research-notes/      exploratory notes (E1-F6 numbered)
  seed/                axioms / philosophy / falsifiability snapshots

REMOVED:
  papers/              ⚠ DELETED ARCHIVE — files removed (commit a02b751);
                       only papers/README.md retained as historical
                       marker + git-history recovery info.

OPERATIONAL:
  tools/               audit scripts (kernel_regress.sh, FORBIDDEN.md, …)
  .claude/skills/      Agent skills
```

### Lean Library Structure (`lean/E213/`)

> Canonical layer definitions in `lean/E213/ARCHITECTURE.md`.

```
Kernel/      18 files (101 thms literally 0-axiom) + Tactic/Omega213
             (Lean-side scaffolding; Kernel-level tactics)
Firmware/    Raw axiom (4-clause) + Atomicity/ sub-cluster (forced
             shape uniqueness; pure-ℕ proofs that don't import Raw)
             + Tools/CertChecker
Hypervisor/  78 files: Lens framework (catamorphism Raw → α) +
             topical sub-clusters: Instances/, Characterisation/,
             Lattice/ (Join/Meet/IndexedJoin), Compose/ (OnLens,
             ImageMinimum, Factoring), Properties/ (refines,
             EquivProperties, ConstLensTotalKernel, etc.),
             Morphism/, Leaves/, Refines/, Kernel/, Universal/,
             plus top-level Initiality.lean + SemanticAtom.lean
Meta/        23 files: true metatheory (UniversalLens family,
             SelfRecognising R1-R4 hierarchy, BitPatternUniqueness,
             RawInductionDemo, AxiomMinimality, CUniquenessBridge)
             + Tactic/{VerifyR4, DeriveR4Codomain}
App/         applications (Simplex)
Math/        484 files (after 2026-05-XX absorption of Research math
             content + Infinity/): Cohomology/, Linalg213/, Real213/
             marathon, CayleyDickson/, Cauchy/, ModArith/, Modulus/,
             Diagonal/, Irrational/, Hyper/, Choice/, Infinity/,
             Tactic/{HurwitzRing, IntSquare, QuadExtension}, Pigeonhole
Physics/     275 files in 18 topical sub-clusters (AlphaEM, Couplings,
             Hadron, Higgs, Mass, Mixing, Nuclear, Cosmology, Atomic,
             Simplex, Basel, FamousCoincidences, YangMills, Capstones,
             Library, Substrate, AtomicCorrespondences, Foundations)
```

**Architectural axis (corrected 2026-05-XX)**: ONE vertical axis
(Kernel/Firmware/Hypervisor/Meta/App).  Math/ and Physics/ are
*topical labels*, NOT a separate axis — every file inside them has a
vertical layer determined by its import closure.  Run
`python3 tools/layer_audit.py` to see each file's mechanical layer.
Previous Research/, Infinity/, Tactic/, Tools/ top-level dirs were
distributed by content + import-derived layer (337+9+11+1 files).

(Counts as of 2026-05-01.  Earlier CLAUDE.md versions listed
sub-project directories `foundations/`, `standard-model/`, `atoms/`,
etc. as "planned" — none were created.  Topical reorg of Phase{2,3,4}
into named sub-folders is a pending architectural task.)

### Branches

  - `main`                                 — base
  - `claude/213-rust-engine-SloKB`         — current work head
  - `claude/review-paper-directory-nDw9L`  — math-track parallel
                                              (frequent cherry-picks
                                               into rust-engine branch)

---

## Workflow

- Session start: read root `HANDOFF.md` first.
- Commit after every meaningful change.  Never amend.
- Physics edits → `lean/E213/Physics/` or `rust-engine/`.
- Math edits → `lean/E213/Math/`.
- Documentation: edit the appropriate top-level dir per layout above.

---

## Key Constants
```
α_GUT = 6/(25π²) ≈ 0.02433    d = 5       c = 2
n_S = 3    n_T = 2              φ = (1+√5)/2
ε = α^(2/3)(1+α) ≈ 0.0860     v_H ≈ 245.6 GeV
S(2) = 5/4    S(∞) = π²/6 ≈ 1.6449
```

## Key Precision Results (0 free parameters)
| Observable | DRLT | Observed | Error |
|-----------|------|----------|-------|
| 1/α_em | 137.036 | 137.036 | **0.0004%** |
| m_p | 938.27 MeV | 938.27 MeV | 0.000% |
| m_μ/m_e | 206.7682837 | 206.7682838 | **0.48 ppb** |
| m_H | 125.28 GeV | 125.25 GeV | **+0.02%** |
| sin²θ₁₃ | 0.0220 | 0.0220 | **-0.07σ** |
| ν m₃/m₂ | 5.712 | 5.71 | **+0.04%** |
| η_B | 6.13×10⁻¹⁰ | 6.1×10⁻¹⁰ | 0.5% |
| Ω_Λ | 0.6850 | 0.685 | **0.0008%** |
| Magic numbers | 2,8,20,28,50,82,126 | 2,8,20,28,50,82,126 | **7/7 exact** |
| E_d (deuteron) | 2.271 MeV | 2.224 MeV | **+2.1%** |
| r₀ (nuc. radius) | 1.262 fm | 1.25 fm | **+0.95%** |
| a_V (volume) | 16.0 MeV | 15.5 MeV | **+3%** |
| a_S (surface) | 18.0 MeV | 16.8 MeV | **+7%** |
| a_C (Coulomb) | 0.685 MeV | 0.71 MeV | **-3.6%** |
| m_π (pion) | 137.6 MeV | 137.3 MeV | **+0.2%** |
| m_ω (omega) | 782.1 MeV | 782.7 MeV | **-0.07%** |
| m_J/ψ | 3081.6 MeV | 3096.9 MeV | **-0.5%** |
| Δ-N split | 295.7 MeV | 294 MeV | **+0.6%** |

## Paper Authorship Rule (when papers are eventually re-introduced)

`papers/` is currently DELETED ARCHIVE (commit a02b751; only
`papers/README.md` retained for historical marker).  For any future
external-communication artifacts (re-built from current 0-axiom
Lean theorems, *not* by reviving the deleted drafts):

- **Author: "Mingu Jeong" only.** Claude is a tool, not an author.
- **In Acknowledgments:** "This work was developed in dialogue with Claude (Anthropic)."
- `\author{...Claude...}` is forbidden. Grounds for arXiv desk reject.
