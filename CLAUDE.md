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

1. **Extremely precise formalized computed values** — a closed 0-sorry 0-axiom Lean theorem matching observations at ppb~ppm precision (e.g., 1/α_em, m_μ/m_e, m_p).
2. **Or formalized new physics that no one can dispute** — a *measurable* proposition closed as a Lean theorem (e.g., N_gen=3, θ_QCD < J·α⁴).

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

## Authors
- Mingu Jeong (Independent Researcher) — theory originator, physical intuition
- Claude (Anthropic) — mathematical formalization, numerical experiments, code
- Equal partnership: Claude must independently think, challenge, and derive.

---

## Repository Architecture

### Single Source of Truth
- **`book/` is the ONLY authoritative theory.** Book > everything else.
- `papers/` = standalone copies for journal submission.
- `research-notes/` = historical drafts (may be superseded).

### Sub-Projects (Independent workspace per field)

| Directory | Prefix | Status | Experiments | Domain |
|-----------|--------|--------|-------------|--------|
| `foundations/` | `FND_` | **ACTIVE** | 37 (FND_001-037) | Derivation chain (math-physics bridge): simplex geometry, variation, f_occ, Grassmannian, Binet–Cauchy, confluence |
| `standard-model/` | `SM_` | CLOSED ✓ | 24 (SM_001-024) | couplings, masses, mixing |
| `atoms/` | `ATM_` | **ACTIVE** | 69 (ATM_001-069) | atoms, periodic table, wedge screening |
| `cosmology/` | `COS_` | STABLE | 3 (COS_001-003) | η_B, Ω_Λ, Webb |
| `cosmic-structure/` | `CST_` | **ACTIVE** | 22 (CST_001-022) | LSS, BH jets, H₀, T_CMB, BBN |
| `critical-line/` | `RH_` | **ACTIVE** | 79 (RH_001-079) | critical line, RH, GRH, L-functions, Galois, Lean |
| `nuclear/` | `NUC_` | **CLOSED** ✓ | 15 (NUC_001-015) | magic numbers, 600-cell, binding |
| `hadron/` | `HAD_` | **CLOSED** ✓ | 9 (HAD_001-009) | meson/baryon spectrum, hyperfine |
| `predictions/` | `PRD_` | **ACTIVE** | 8 (PRD_001-009) | unmeasured predictions (JUNO, θ_QCD, Berry phase) |
| `quantum-gravity/` | `QG_` | **ACTIVE** | 7 (QG_001-007) | spacetime emergence, holographic |
| `yang-mills/` | `YM_` | **ACTIVE** | 0 (Lean ~58 thms) | mass gap, NS regularity, Lean 4 formalization |
| `discrete-harmonic/` | `DHA_` | **ACTIVE** | 19 (DHA_001-019) | discrete harmonic analysis, spectrum, S₅ representation theory |
| `drlt-elements/` | `ELM_` | **ACTIVE** | 0 (Lean 7 files 26 thms) | elements: Entity→Eq→Logic→Nat→Arith→Order→Bridge |

### Sub-Project Required Structure
```
{sub-project}/
  CLAUDE.md          — field context, constants, experiment list (required)
  HANDOFF.md         — status, open problems, next steps (required)
  experiments/       — {PREFIX}_NNN_name.py (required)
  results/           — experiment output (required)
  theory/            — theory documents .tex/.md (optional)
  lib/               — field-specific library (optional)
```

### Shared Infrastructure
```
books/             — narrative books (math/, physics/)
papers/            — standalone .tex for journal submission (16 papers + drlt-book/)
.claude/skills/    — Agent skills
```

### Lean Library Structure (lean/E213/)
```
Kernel/     ★ deep-embedded 213 kernel (14 files, 101 theorems, 0 axiom)
Physics/    physics formalization (227 files)
Research/   research / exploratory proofs (331 files)
Math/       mathematics (8 files)
Firmware/   Raw axiom layer: Raw, RawLevels, RawSwap (13 files)
OS/         Atomicity + canonical structures (8 files)
App/        applications (1 file)
Hypervisor/ cross-layer bridge (1 file)
Infinity/   limit / compactification (9 files)
Meta/       meta-theory utilities (9 files)
Tactic/     custom tactics (10 files)
```

---

## Naming
- Experiments: `{PREFIX}_{NNN}_{desc}.py` (inside sub-project/experiments/)
- Results: `EXP_{PREFIX}_{NNN}_{Title}.txt` (auto-generated, sub-project/results/)
- New sub-project: prefix + CLAUDE.md + HANDOFF.md + experiments/ + results/

---

## Organization
- Experiments/results go inside sub-projects only. No EXP_*.txt in root results/.
- Theory consolidated in book/. Sub-projects are workspaces.
- Session start: read root HANDOFF → then sub-project HANDOFF in order.

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

## Workflow
- After editing book/, sync math/ + physics/ and regenerate single .tex.
- Commit after every meaningful change. Never amend.

## Paper Authorship Rule
- **Author: "Mingu Jeong" only.** Claude is a tool, not an author.
- **In Acknowledgments:** "This work was developed in dialogue with Claude (Anthropic)."
- `\author{...Claude...}` is forbidden. Grounds for arXiv desk reject.
