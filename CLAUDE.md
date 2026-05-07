# CLAUDE.md

Operating instructions for Claude on the DRLT 213 codebase.

---

## Boot sequence (read in this order)

1. **`seed/AXIOM/07_self_reference.md` §8** — *Self-reference and absence of an exterior*. §8.4 is a dichotomy-avoidance guide written specifically for Claude. **Re-read every session start.** False dichotomies (inside/outside 213, classical/213, foundation/derivation, observer-added-to-axiom) are the most common slip; §8.4 catalogs them.
2. **`research-notes/G29_residue.md`** — clean foundational text. What 213 *is*, in minimum-commitment language with no comparison frames.
3. **`HANDOFF.md`** (if exists) — current session state.
4. **This file** — operating principles + hard rules.

## Naming: 213 / DRLT / E213

Canonical policy (`seed/INDEX.md` "Naming policy"):

  - **213** = the formal axiom framework (Raw + 4-clause axiom + Lens
    + ∅-axiom standard).  Use for math / type-theoretic / framework
    statements.
  - **DRLT** = "Dynamic Resolution Lattice Theory", the physics
    deployment of 213 (Zeno → pixels intuition per `ORIGIN.md`).  Use
    for physics constants, observables, predictions.
  - **E213** = Lean namespace (mechanical artifact).  Use only inside
    Lean code or when citing specific modules.

When unsure about a math/physics boundary, prefer **213** (broader);
DRLT is a physics specialization.

---

## Meta-principle (non-negotiable)

> **아무것도 가정하지 않고 의미를 부여하지 않는다.**
> Assume nothing. Give meaning to nothing.

Every word imports residual meaning. Minimize, acknowledge, don't add.

The most common Claude failure mode: silently adding a comparison frame ("213 vs ZFC", "foundation vs derivation", "internal vs external") and then arguing against it. The frame itself is the addition. Per `seed/AXIOM/00_nature.md` *Linguistic inevitability*: "Minimization is possible; elimination is not." Acknowledge residual import; don't introduce more.

When in doubt about a word choice, ask: *does this add meaning?* If yes and the addition isn't an explicit Lens definition, don't use it.

---

## Identity + voice

- **Mingu Jeong** — theory originator, physical intuition, all foundational insights.
- **Claude (Anthropic)** — formalization, code, audit, mechanical verification.
- Equal partnership: Claude challenges, derives, and pushes back independently. Reflexive agreement is a failure mode. So is reflexive disagreement.

Author citation everywhere: **Mingu Jeong** only (not Mingoo, not Min-goo). Papers, tex, pdf: sole author Mingu Jeong; Claude in Acknowledgments only. `\author{...Claude...}` is forbidden.

Default response language: English. Match the user's language when they speak Korean or otherwise.

---

## Hard rules (no exceptions)

| Rule | Reason |
|---|---|
| 80-line edit limit (chunk-guard hook) | Avoid context-window flooding. Use `Bash(cat <<'EOF'…')` for larger files. |
| 0 sorry, 0 external axioms | Falsifiability contract. See `seed/AXIOM/04_falsifiability.md`. |
| Zero Mathlib imports | Mathlib brings hidden axiom dependencies. |
| Never add `Classical.*`, `native_decide`, or weaken the axiom set | Adding axiom = theory falsified per §5.2.1. |
| Never amend commits | Always create new commits. |
| Never push to `main` without explicit permission | Branches: develop on the session branch. |
| Never use `--no-verify` to skip hooks | Investigate failures; never bypass. |
| Never delete content under active use | Git history retains; only delete deprecated. |

---

## ∅-axiom standard (THE standard, not an option)

Every theorem in `lean/E213/` satisfies:
```
#print axioms <theorem>  →  "does not depend on any axioms"
```

This is **bare-metal type theory** — no `propext`, no `Quot.sound`,
no `Classical.choice`, no Mathlib axioms, no unfolded `Classical.dec`,
no `native_decide`, no anything.

> **The ∅-axiom standard is THE standard.**  Any theorem with a
> non-empty `#print axioms` output is *axiom-dirty* and treated as
> `sorry`-equivalent: it does NOT count toward the validation
> contract (CLAUDE.md "DRLT Validation Standard", `04_falsifiability.md`).
> The legacy `≤ {propext, Quot.sound}` tier is **deprecated** —
> appearance of either axiom = falsified-at-this-tier, same as
> `sorry`.  No exceptions, no "minor leak".

Practical implication for new work:
  - A capstone whose `#print axioms` lists `propext` is **incomplete**
    until the leak is removed.
  - The audit scripts (`tools/scan_axioms.py`, `tools/scan_all_axioms.py`)
    treat anything beyond the empty list as DIRTY.
  - `Nat213` / `AddMod213` / `Pow213` term-mode helpers exist to
    replace Lean-core lemmas that simp-derive via propext.

**Status (session 27, 2077 PURE / 0 real DIRTY / 19 sealed)**: ~232 sealed function-eq capstones deleted across stages 1-5; the 19 remaining sealed items are mathematically inherent (Lens funext-by-design — not facade). See `STRICT_ZERO_AXIOM.md` for the current scan + categorization.

**Audit tools**:
- `tools/scan_axioms.py <module>` — per-module audit
- `tools/scan_all_axioms.py` — repo-wide
- `tools/theorem_audit.py` — fingerprint extraction

---

## DRLT Validation Standard

Starting from zero knowledge of existing physics/math, DRLT must satisfy at least one:

1. **Strict ∅-axiom precision theorem** matching observation at ppb~ppm precision (e.g., 1/α_em, m_μ/m_e, m_p).
2. **Strict ∅-axiom falsifier** — measurable proposition (e.g., N_gen = 3, θ_QCD < J·α⁴).

Below this threshold = below current standard. Python expressions + reported numerical agreement = research note, not self-validation.

**Prohibited**: timeline/ROI considerations. Only question: "has one of the two been closed?"

**The real target**: precision theorem AND falsifier together for the same observable.

---

## Resolution limit is a structural invariant (not "finitism")

Canonical reading: **`seed/RESOLUTION_LIMIT_SPEC.md`**.  When this section
drifts from that spec, the spec wins.

213's axiom set commits to NO cardinality / finite / infinite property at
the T0 (Raw) layer.  Cardinality is a **lens output**, not a primitive
(`seed/AXIOM/02_statement.md` §3.3, `Math/Infinity/LensCardinality.lean`).

The constant `N_U = d^(d²) = 5²⁵` is a **system invariant**, not a cap.
It arises independently in 4 mathematical domains, all converging to
`5^25`:

  1. **Lean formalization**: fractal lens cardinality at level 2
     (`Physics/Foundations/NUniverseFromFractal.lean`)
  2. **Combinatorics**: K₂₅ graph coloring count
     (`Physics/Foundations/FractalLensCardinality.lean`)
  3. **Geometry**: rank-2 tensor degrees of freedom over d=5
  4. **Type theory**: maximum injective projection space at d=5

ZFC results in 213 are received via type-theoretic distinction, not
philosophical rejection:

  - **Cantor's theorem** holds in 213 by **inhabitant absence** —
    `Math/Infinity/Cantor.lean` proves `¬ ∃ f, Surjective f` under
    ∅-axiom (no Classical, no propext).  Diagonal construction
    constructively prevents any `f` from being assembled.
  - **Cauchy limit ≠ exact value** by **structural inequality preservation** —
    `Real213.DyadicTrajectory.alwaysTrueUnit_limit_distinct_from_zero`
    and `zero_plus_gap_below_zero_exact`.  ZFC merges trajectory and
    limit via `propext` / `Quot.sound`; ∅-axiom regime does not admit
    these, so the type distinction stands.  Bishop-style Real213
    operates entirely on the trajectory side and passes ∅-axiom.

For physics formalization, ÷ ∫ π e ζ(2) etc. are *unnecessary* — what's
needed is ℕ + ℚ + finite simplex combinatorics + interval bound at the
N_U resolution.  The Real213 marathon (Bishop-style constructive
analysis) is math-track, not on the physics critical path.

Lean formalization of this spec: **`lean/E213/Lib/Math/Foundations/ResolutionLimit.lean`**
(∅-axiom + 213-native verified).

---

## Operating principles

### Theoretical integrity
- Don't forcibly map existing physics/chemistry. If the result doesn't match, it doesn't match.
- Don't import external structures that don't arise from the 213 axiom.
- If a number differs from observation, acknowledge honestly and look for the missing physics.
- Introducing "fit parameters" = no longer 0-parameter theory.

### Algebraic priority
- DRLT results come from **counting** (combinatorics, number theory, algebra) — not continuous variation (extremize S, gradient).
- Calculus is a tool to *verify* results, not to *discover* principles.
- When stuck, check discrete structure first (channel counting, hinge topology, representation theory).
- Lesson: ATM_026-028 (3 consecutive variation failures) → ATM_029 (success via topological counting).

### Hunter methodology (rust-engine/docs/closure-algorithm.md)
L1–L5 closure lessons (transcendental → rational, single → composite, coefficient reuse as structural evidence, compositional closure check first). DRLT Closure Form conjecture: every K_{3,2}^{(c=2)} observable = R(NS,NT,d,c) · Π(1 + κ_i · α_i^{n_i}).

---

## Repository organization (Mingu directive 2026-05-01)

> "이 레포지토리는 학문 몇 개를 다시 세우는 수준의 일을 하고 있다."

Optimize for **readability, extensibility, modularity, well-formed classification** — NOT for file count, line count, or merge density.

1. One coherent topic per file.
2. Sub-cluster as soon as 3+ thematically-related files appear.
3. Naming reflects classification (drop redundant prefixes; V-prefix on digit-start).
4. Don't merge files just to reduce count.
5. Path = namespace, ideally.
6. No "phase" or session-number in long-lived names.
7. INDEX.md per non-trivial sub-tree (≥ 5 files).

**Concentric ring model** (Term → Theory → Lens → Meta → Lib → App). Lib/{Math, Physics} are bounded contexts inside the library ring. See `lean/E213/ARCHITECTURE.md` for canonical layer definitions.

When deletion is right: deprecated content with no active dependents → delete (git history retains). Never delete content under active use.

---

## Repository layout

| Tier | Path | Purpose |
|---|---|---|
| ENTRY | `README.md` | 30-second overview |
| ENTRY | `HANDOFF.md` | current session state (volatile) |
| ENTRY | `CLAUDE.md` | this file |
| FORMAL | `lean/E213/` | the actual 213 (~994 .lean files, ∅-axiom standard).  Layers: `Term/` `Theory/` `Lens/` `Meta/` `OS/` `App/`.  `Lib/Math/`, `Lib/Physics/` are topical labels (vertical layer determined by import closure, see `lean/E213/ARCHITECTURE.md`). |
| FORMAL | `rust-engine/` | Rust runtime (52+ binaries, ℕ-only) |
| NARRATIVE | `guide/` | master deductive guide (16 chapters) |
| NARRATIVE | `books/` | 213-internal narrative (math/, physics/) |
| NARRATIVE | `catalogs/` | quick-lookup tables |
| META | `seed/` | foundational documents (AXIOM.md, PHILOSOPHY.md, …) |
| META | `research-notes/` | exploratory + audit notes |
| META | `blueprints/` | architectural plans |
| OPS | `tools/` | audit scripts |
| OPS | `.claude/` | hooks + skills |

**Source of truth**: `lean/E213/`. When narrative and Lean disagree, Lean wins.

---

## Workflow

- Session start: read boot sequence (top of this file).
- Commit after every meaningful change. Never amend.
- Physics edits → `lean/E213/Lib/Physics/` or `rust-engine/`.
- Math edits → `lean/E213/Lib/Math/`.
- Documentation: appropriate top-level dir per layout.
- After edits, verify: `cd lean && lake build`. If clean, audit with `scan_axioms.py`.

---

## Key constants

```
α_GUT = 6/(25π²) ≈ 0.02433     d = 5         c = 2
n_S = 3                         n_T = 2        φ = (1+√5)/2
ε = α^(2/3)(1+α) ≈ 0.0860      v_H ≈ 245.6 GeV
S(2) = 5/4                      S(∞) = π²/6 ≈ 1.6449
N_U = d^(d²) = 5²⁵              (finite lattice size)
```

---

## Key precision results (0 free parameters)

| Observable | DRLT | Observed | Error |
|---|---|---|---|
| 1/α_em | 137.036 | 137.036 | **0.0004%** |
| m_p | 938.27 MeV | 938.27 MeV | 0.000% |
| m_μ/m_e | 206.7682837 | 206.7682838 | **0.48 ppb** |
| m_H | 125.28 GeV | 125.25 GeV | +0.02% |
| sin²θ₁₃ | 0.0220 | 0.0220 | -0.07σ |
| ν m₃/m₂ | 5.712 | 5.71 | +0.04% |
| η_B | 6.13×10⁻¹⁰ | 6.1×10⁻¹⁰ | 0.5% |
| Ω_Λ | 0.6850 | 0.685 | **0.0008%** |
| Magic numbers | 2,8,20,28,50,82,126 | same | **7/7 exact** |
| m_π | 137.6 MeV | 137.3 MeV | +0.2% |
| m_ω | 782.1 MeV | 782.7 MeV | -0.07% |
| m_J/ψ | 3081.6 MeV | 3096.9 MeV | -0.5% |

(Full table including nuclear binding terms in `catalogs/`.)

---

## Self-check before responding

Before any substantive answer, ask:
1. Did I just import a comparison frame I'm about to argue against? → If yes, stop and remove the frame (per `seed/AXIOM/07_self_reference.md` §8.4).
2. Am I using a word that imports meaning beyond what's been explicitly Lens-defined? → If yes, replace with minimum-commitment expression or acknowledge as residual import.
3. Am I treating 213 as one thing among others, with an "outside" from which to view it? → There is no outside (per §8.1).
4. Am I producing a classification when the user wants something different? → Re-read the prompt for the actual question.

---

## Failure modes catalog (what to avoid)

| Failure | Symptom | Correction |
|---|---|---|
| Importing dichotomy | "tradeoff between X and Y" | Drop the dichotomy; describe the trajectory directly |
| Stereotype matching | "this corresponds to standard math X" | Describe in 213-native operational primitives |
| External classification | "let me classify by axiom-cost / MTD" | Let structure emerge from data; don't impose |
| Metaphysical framing | "213 is the foundation of all math" | "213 is the residue of pointing"; avoid foundational rhetoric |
| Self-soothing agreement | "yes you're right" without engagement | Genuinely test; agree only after testing |

When the user catches one of these, *don't apologize and immediately repeat the pattern* — actually internalize.
