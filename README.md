# 213 Library

> Derive all of mathematics and physics from *primitive distinction* —
> Lean 4 core only, Mathlib-free, ℕ-only Rust verification engine.

## What It Is

**213** = Starting from the *minimal residue* with a 3-clause Raw axiom
(plus directionless slash_comm).

```
DRLT (Dynamic Resolution Lattice Theory)
  = Raw axiom (a, b, slash, slash_comm)
  + Lens framework
  → Atomicity (d = 5 unique, NS = 3, NT = 2 forced)
  → K_{3,2}^{(c=2)} graph (canonical)
  → Mathematics + Physics derived
```

## Core stakes

- **0 sorry, 0 Mathlib, 0 Classical, 0 native_decide, 0 axiom**
- ★ **∅-axiom is THE standard** — every theorem must satisfy
  `#print axioms T → "does not depend on any axioms"`.  Any
  non-empty axiom list (incl. `propext`, `Quot.sound`) is
  `sorry`-equivalent and does not count toward closure.  See
  `seed/AXIOM/08_falsifiability.md` §8.2 + `CLAUDE.md`
  "∅-axiom standard".
- ★ **Kernel layer ∅-axiom**: deep-embedded `Term` system; neither
  propext nor Quot.sound is load-bearing.
  Verify: `./tools/kernel_regress.sh`
- *No numerical analysis* — ℕ + ℚ-as-(ℕ, ℕ) only.  π via Wallis brackets,
  ζ(2) via Basel — no transcendental hardcodes.
- *Mathlib-free* throughout.
- *Independent Rust verification engine* — 53 binaries, 184 tests,
  94 Lean-theorem citations resolved at theorem-id level.

## Headline results — read honestly

**∅-axiom purity (what the Lean kernel guarantees) is not the same as "the
headline precision is a PURE theorem".** This table keeps the two apart, per
row: *what the Lean actually proves* vs *what a finer number in a docstring
claims*, and whether a result is a **parameter-free ratio** or an **absolute**
(which needs an input scale, as any theory does). Audited per the
headline-precision-scope frontier; methodology:
`VERIFICATION_SPINE.md` §0 + `DEGREES_OF_FREEDOM_LEDGER.md`.

### A. Parameter-free — dimensionless ratios + exact combinatorics (no input scale)

| Observable | DRLT form | What Lean proves (PURE) | Match |
|---|---|---|---|
| **Koide Q** | `NT/NS = 2/3` | exact ratio (`koide_atomic`) | ~3 ppm, **0 param** |
| **1/α_em** | `60·ζ(2)+30+25/3+α_GUT corr.` | structural `137.035999111` = CODATA `…084` + 27e-9 (`invAlphaEm_precision_theorem`) | **0.2 ppb, PURE** ¹ |
| m_H/v_H | `1/c = 1/2` (+ α_GUT corr.) | `1/c` exact ratio | leading exact |
| m_μ/m_e | `(NS/NT)·(1/α_em)·P·(1+Σδ)` | leading bracket `205 ∈ [197,206]` | 0.49 ppb is **docstring**, not the theorem ² |
| Magic numbers 2,8,20… | HO closed form | exact | EXACT |
| Muon prefactor | `(NS²−1)(d²−1) = 192` | exact integer | EXACT |

¹ α_em's ppb precision *is* a PURE theorem; the residual is in the *assembly*
of the formula (assignment / Gram form), tracked + mostly closed in
`DEGREES_OF_FREEDOM_LEDGER.md`.
² m_μ/m_e's PURE theorem proves only the leading integer bracket; the sub-ppb
number comes from the docstring formula (Dyson tail `P` + δ's) and inherits
α_em's bracket.

### B. Absolute masses / energies — require an input scale

| Observable | DRLT | Input scale | What Lean proves |
|---|---|---|---|
| m_p ≈ 938.27 MeV | `NS·Λ_QCD·P(α_GUT·NS/d)` | **Λ_QCD ≈ 308 MeV** (docstring; not atom-derived) | 0.1% bracket; real content is the *ratio* `m_p/Λ_QCD = NS·P = 3.04` |
| IE(H) ≈ 13.606 eV | `m_e·α²/2` (textbook) | **CODATA m_e** | ~0.1% bracket; DRLT's only input beyond textbook is α |

The dimensionless-ratio predictions (Koide, m_H/v_H, m_μ/m_e, α_em) stand on
their own; the **absolute** sub-ppm/ppb figures reflect a correct ratio times a
measured scale, not a parameter-free absolute.

## DRLT Validation Standard pairings

**17 of 23 observables** in `catalogs/physics-constants.md` have both
a PURE precision theorem AND a PURE falsifier bracket (74% closure).
(Per the headline audit above, "PURE precision theorem" often means a
*bracket* at the stated width, not the docstring central value — see the
headline-precision-scope frontier for the per-row scope.)
Falsifier catalog F1–F20 in `catalogs/falsifiers.md`.  Remaining
unpaired: Koide 2/3, η_B, m_t/m_c, m_p/m_e ≈ 6π⁵, M_Pl/v_H,
muon prefactor 192 (precision only; falsifier follow-up).

## Famous coincidences elevated to derivations

| Coincidence | Year | DRLT form |
|---|---|---|
| 1/α_em ≈ 137 (Eddington) | 1929 | 60·ζ(2) + 30 + 25/3 + α_GUT corr. |
| m_p/m_e ≈ 6π⁵ (Lenz) | 1951 | NS · NT · π⁵ |
| Koide 2/3 | 1981 | NT / NS |
| Hierarchy M_Pl/v_H | 1980s | d^(d²) / (d+1) = 5^25/6 |

## Universal Lens metatheory

```
expSumLens : Lens (ℕ × ℕ)        Function.Injective expSumLens.view
q213Lens   : Lens (Q213 × Q213)  Function.Injective q213Lens.view
                                  (Q213 := Term × Term, 213-native ℚ)
```

Both at ∅-axiom (audit: `tools/scan_axioms.py`).  Every Raw element
is uniquely encoded as a pair of 213-native rationals via a
symmetric commutative magma operation — the formal expression of
the G1 thesis ("213 is the precondition for any describing").

## Quick navigation (INDEX files)

For a *5-second* entry into any sub-area, read its `INDEX.md`:

| Dir | INDEX | Purpose |
|---|---|---|
| `seed/` | `seed/INDEX.md` | axioms + philosophy reading order |
| `lean/E213/` | `lean/E213/ARCHITECTURE.md` (theory) + `lean/E213/INDEX.md` (navigation) | canonical layer definitions + capstone map |
| `catalogs/` | `catalogs/README.md` | grep-able lookup tables |
| `research-notes/` | `research-notes/INDEX.md` | numbered exploratory notes |
| `blueprints/` | `blueprints/INDEX.md` | math/physics/meta blueprints |
| `rust-engine/` | `rust-engine/docs/architecture.md` | runtime + binaries |

Top-level Lean theorem index: `CAPSTONE_INDEX.md`.
Strict-zero-axiom achievements: `STRICT_ZERO_AXIOM.md`.
Current session state: `HANDOFF.md`.
Agent guardrails: `LESSONS_LEARNED.md`.

**Quantitative-architecture entry**:
    view of corpus shape, recursor inventory, citation hubs.
    registry from the meta-scan tree (executor entry).
  · `catalogs/abstraction-candidates.md` — per-item status tracker.
  · `catalogs/falsifier-roster.md` — 135 auto-discovered falsifiers
    (mined via decide-negation scan).
  · `seed/THEOREM_METHODOLOGY_SUITE.md` §TH-2 — "X is derived from Raw"
    α / β / γ three-reading distinction.

## Directory

```
seed/            axioms + philosophy + falsifiability
lean/E213/       Lean 4 formal library (~2000 files; exact: tools/lean_summary.py)
                 — see `lean/E213/ARCHITECTURE.md` for canonical
                   theoretical layer definitions (4 ring + Meta)
  ├── Term/      Raw 의 구현체 (deep-embedded Tree
  │              substrate + ∅-axiom Bool comparators / soundness
  │              bridges / Demo / MonomialAxioms).  Theory 가
  │              사용할 base API.  ★ literally 0-axiom.
  ├── Theory/    213 axiom 자체 (Raw + 4-clause
  │              definitional commitments) + Atomicity (forced
  │              d=5, (NS,NT)=(3,2)) + CDDouble + Congruence
  │              + ParenthesizationDistinct.  Term API 만 사용.
  │              (Bool213 / Nat213 / RawCut are Lens-layer
  │              catamorphism artifacts.)
  ├── Lens/      Lens framework (catamorphism Raw → α)
  │              + Algebra/AxiomLenses/Bool213/Cardinality/Compose/
  │              Congruence/Instances/Lattice/Number/Properties/
  │              SyntacticInternalization/Universal sub-clusters.
  │              Theory API 만 사용.
  ├── Lib/Math/  42 sub-clusters: CayleyDickson,
  │              Real213, SignedCut, Probability, Cohomology,
  │              DyadicFSM, HodgeConjecture, Analysis,
  │              Linalg213, Cauchy, ModArith, Modulus, Irrational,
  │              Hyper, Choice, Polynomial213, Trajectory, …
  │              Lens API 만 사용.
  ├── Lib/Physics/ 18 sub-clusters: AlphaEM, Couplings,
  │              Hadron, Higgs, Mass, Mixing, Nuclear, Cosmology,
  │              Atomic, Simplex, Basel, YangMills, Capstones,
  │              AtomicBase, Foundations, Certificates, Quantum,
  │              Symmetry.  Lens API 만 사용.
  └── Meta/      ring-independent Lean 4 bridge.
                 SelfRecognising (CommBinary/NonVanishing/
                 Conjugation Codomain typeclass tower),
                 AxiomMinimality{,Capstone}, LensInternality,
                 BitPatternUniqueness + Tactic/ (Nat213, Mod213,
                 Fin213, Pow213, Omega213, QuadNorm, PureGuard,
                 NativeGuard, List213, …) + Nat/Int213/Algebra213
                 helpers.  Universal-Lens witnesses live in
                 `Lens/Universal/Witnesses/`.
rust-engine/     Independent ℕ-only verification (53 binaries,
                 184 tests, 94 citations)
blueprints/      math/14 + physics/14 + meta/2 (status snapshots)
books/           narrative hierarchy
  └── math/      analysis213 + number-theory-213 + cohomology-213
                 + linalg-213 + probability-213 + universal-lens-213
  └── physics/   periodic-table + diamond crystal narrative
catalogs/        lookup tables (atomic integers, constants,
                 periodic table, falsifiers)
tools/           automation (audit, regress, FORBIDDEN)
research-notes/  research notes
```

## Build

```bash
cd lean/
lake build E213
# → builds the framework rings (Term / Theory / Lens / Meta +
#   Pigeonhole).  Fast, minimal-axiom check.

lake build E213.Lib.Math E213.Lib.Physics
# → builds the content library (Lib/Math + Lib/Physics).
#   Slower, but exercises everything; required after any
#   refactor of List213 / Meta tactics / Real213 / etc.

# → ∅-axiom, no Mathlib, no Classical, no sorry, no native_decide.
# Anything with a non-empty `#print axioms` output = sorry-equivalent.
```

## Theory book

```
theory/THEORY_BOOK.md     Single linearised reading path from
                          seed/AXIOM/ to GRA Phase 22's
                          Lens.Unified capstone (math-only,
                          ~1200 lines, 8 parts + appendices).
theory/math/algebra/gra_book.md   GRA textbook (Ch.0–9 + appendices),
                          the universal meta-structure of 213.
theory/<area>/*.md        Per-area narrative chapters (math /
                          physics / lens / meta / essays).
```

See `theory/INDEX.md` for the chapter catalog and
`theory/THEORY_BOOK.md` "Reading paths" appendix for ordered
entry points.

## Authors

- Mingu Jeong (Independent Researcher)
- Claude (Anthropic): formalization, Acknowledgments
- 0 sorry, 0 external axioms

## License

This is a **research repository, not an open-source library**.
Check the license before use.

| Scope | License | Meaning |
|---|---|---|
| `lean/`, `tools/`, `.claude/`, `rust-engine/` (code) | **PolyForm Noncommercial 1.0.0** | Free academic/non-commercial use & modification; commercial use *prohibited* |
| `books/`, `blueprints/`, `seed/`, `catalogs/`, `research-notes/` (prose) | **CC BY-NC-ND 4.0** | Attribution + non-commercial + *no derivatives* |

Details: [`LICENSE`](LICENSE) (code) · [`LICENSE-DOCS`](LICENSE-DOCS) (prose)

Academic citation, research reproduction, and educational use are welcome.
Commercial fork / productization / unauthorized translation / unauthorized modification is prohibited.

Copyright © 2026 Mingu Jeong.
