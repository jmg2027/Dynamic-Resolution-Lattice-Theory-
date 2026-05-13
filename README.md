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
  `seed/AXIOM/04_falsifiability.md` §5.2.1 + `CLAUDE.md`
  "∅-axiom standard".
- ★ **Kernel layer ∅-axiom**: deep-embedded `Term` system; neither
  propext nor Quot.sound is load-bearing.
  Verify: `./tools/kernel_regress.sh`
- *No numerical analysis* — ℕ + ℚ-as-(ℕ, ℕ) only.  π via Wallis brackets,
  ζ(2) via Basel — no transcendental hardcodes.
- *Mathlib-free* throughout.
- *Independent Rust verification engine* — 53 binaries, 184 tests,
  94 Lean-theorem citations resolved at theorem-id level.

## Headline results (sub-ppm physics)

| Observable | DRLT | Observed | Δ |
|---|---|---|---|
| 1/α_em | 137.0359895 | 137.0359991 | **0.07 ppm** |
| m_μ/m_e | 206.7682837 | 206.7682838 | **0.49 ppb** |
| m_p | 938.271472 MeV | 938.2700 MeV | **1.56 ppm** |
| H ionization | 13.605693 eV | 13.605693 eV | **4.3 ppb** |
| Magic numbers 2,8,20 | exact | exact | EXACT |
| Muon prefactor 192 | exact | 192 | EXACT |

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
| `papers/` | `papers/README.md` | ⚠ DELETED ARCHIVE (see README for git recovery) |
| `rust-engine/` | `rust-engine/docs/architecture.md` | runtime + binaries |

Top-level Lean theorem index: `CAPSTONE_INDEX.md`.
Strict-zero-axiom achievements: `STRICT_ZERO_AXIOM.md`.
Current session state: `HANDOFF.md`.
Agent guardrails: `LESSONS_LEARNED.md`.
Active branch split (transient): `BRANCH_MERGE_GUIDE.md`.

## Directory

```
seed/            axioms + philosophy + falsifiability
lean/E213/       Lean 4 formal library (~1127 files)
                 — see `lean/E213/ARCHITECTURE.md` for canonical
                   theoretical layer definitions (4 ring + Meta
                   since 2026-05-12)
  ├── Term/      12 files — Raw 의 구현체 (deep-embedded Tree
  │              substrate + ∅-axiom Bool comparators / soundness
  │              bridges / Demo / MonomialAxioms).  Theory 가
  │              사용할 base API.  ★ literally 0-axiom.
  ├── Theory/    41 files — 213 axiom 자체 (Raw + 4-clause
  │              definitional commitments) + Atomicity (forced
  │              d=5, (NS,NT)=(3,2)) + Closed (Bool213, Nat213,
  │              RawCut) + Nat213/Tower/CDDouble.  Term API 만 사용.
  ├── Lens/      121 files — Lens framework (catamorphism Raw → α)
  │              + Algebra/AxiomLenses/Cardinality/Compose/
  │              Instances/Lattice/Properties/Universal sub-clusters.
  │              Theory API 만 사용.
  ├── Lib/Math/  743 files (43 sub-clusters): CayleyDickson,
  │              Real213, SignedCut, Probability, Cohomology,
  │              DyadicFSM, HodgeConjecture, Analysis,
  │              Linalg213, Cauchy, ModArith, Modulus, Irrational,
  │              Hyper, Choice, Polynomial213, Trajectory, …
  │              Lens API 만 사용.
  ├── Lib/Physics/ 165 files (17 sub-clusters): AlphaEM, Couplings,
  │              Hadron, Higgs, Mass, Mixing, Nuclear, Cosmology,
  │              Atomic, Simplex, Basel, YangMills, Capstones,
  │              Substrate, Foundations, Certificates, …
  │              Lens API 만 사용.
  └── Meta/      37 files — ring-independent Lean 4 bridge.
                 SelfRecognising (CommBinary/NonVanishing/
                 Conjugation Codomain typeclass tower),
                 AxiomMinimality{,Capstone}, LensInternality,
                 BitPatternUniqueness + Tactic/ (Nat213, Mod213,
                 Fin213, Pow213, Omega213, QuadNorm, PureGuard,
                 NativeGuard, …) + Nat/Int213/Algebra213 helpers.
                 Universal-Lens witnesses moved to
                 `Lens/Universal/Witnesses/` 2026-05-13.
rust-engine/     Independent ℕ-only verification (53 binaries,
                 184 tests, 94 citations)
blueprints/      math/14 + physics/14 + meta/2 (status snapshots)
books/           narrative hierarchy
  └── math/      analysis213 + number-theory-213 + cohomology-213
                 + linalg-213 + probability-213 + universal-lens-213
  └── physics/   periodic-table + diamond crystal narrative
papers/          ⚠ DELETED ARCHIVE (papers/README.md only; recoverable
                  from git history at commit a02b751)
catalogs/        lookup tables (atomic integers, constants,
                 periodic table, falsifiers)
tools/           automation (audit, regress, FORBIDDEN)
research-notes/  research notes
```

## Build

```bash
cd lean/
lake build E213
# → ∅-axiom, no Mathlib, no Classical, no sorry, no native_decide.
# Anything with a non-empty `#print axioms` output = sorry-equivalent.
```

## Math books

```
books/math/
├── analysis213.md        Undergraduate year-1 calculus (100%)
├── number-theory-213.md  Pell, Pisano CRT, Legendre lens,
│                          Universal Lens metatheory
├── cohomology-213.md     K_{3,2}^{(c=2)}, Δ⁴ Leibniz,
│                          Hodge ⋆⋆, fractal α_GUT
├── linalg-213.md         Paper 1 Chiral Compression (rank ≤ 5)
├── probability-213.md    measure-on-cuts blueprint
└── universal-lens-213.md G1 universal-lens paper-style exposition
```

See `books/math/INDEX.md` for reading order.

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
| `books/`, `papers/`, `blueprints/`, `seed/`, `catalogs/`, `research-notes/` (prose) | **CC BY-NC-ND 4.0** | Attribution + non-commercial + *no derivatives* |

Details: [`LICENSE`](LICENSE) (code) · [`LICENSE-DOCS`](LICENSE-DOCS) (prose)

Academic citation, research reproduction, and educational use are welcome.
Commercial fork / productization / unauthorized translation / unauthorized modification is prohibited.

Copyright © 2026 Mingu Jeong.
