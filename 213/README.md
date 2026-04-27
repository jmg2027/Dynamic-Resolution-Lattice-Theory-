# 213

**A minimal foundational system: Raw + Lens.**

213 is a 3-clause axiom and a Lens framework for observation,
formally verified in Lean 4 core (no Mathlib, 0 sorry, 0 external
axioms beyond `propext` and `Quot.sound`).

## The axiom

> 1. *Something exists.*
> 2. *To know what it is, another something is required.*
> 3. *That other something is also a something.*

Clauses (1)+(3) give at least two somethings (`a`, `b`); clause (2)
is the primitive *distinction* operation, applied recursively
(`Raw.slash x y` with `x ≠ y`).  No equality, no order, no set
theory pre-imposed — those arise as Lens-level outputs.

## What the framework establishes

- **Strict minimum** (`Research/AxiomMinimality.lean`, 4 cases).
  Raw axiom 의 어떤 clause (a, b, slash, distinctness) 제거
  / 약화 시 framework 가 trivial / static / void 로 collapse.
  Raw axiom 이 "distinguishable + generative" framework 의
  framework-internal strict minimum.
- **Distinguishing-framework hub** (`Research/SemanticAtom.lean`).
  `HasDistinguishing` typeclass abstraction.  Raw 가 이 abstraction
  의 instance, `universalMorphism` 으로 임의 instance 에 fold-
  derived morphism.  `Prop` 도 instance (Xor / Iff connectives).
- **Encoding-artifact independence** (`Research/CmpIndependence.lean`).
  Two different total orders on the underlying `Tree` give the
  same Raw up to isomorphism — the encoding choice has no
  mathematical consequence.
- **ZFC reductions** (`Research/ChoiceResolved.lean`,
  `Research/UniversalQuotLens.lean`).  "Choice" becomes "Lens
  specification": for any slash-congruence `E`, an explicit Lens
  with kernel `E` exists.  No `Classical.choice`.
- **Cauchy completeness** (`Research/LensCauchy.lean`,
  `Research/GenericFamilyCauchy.lean`).  Family-Cauchy sequences
  have well-defined limit assignments via Lens projections.
- **Concrete irrationals** as Cauchy demonstrations:
  - `Research/Sqrt2Cut.lean` + `Research/PellSeq.lean` — √2 (algebraic).
  - `Research/Padic.lean` — p-adic ℤ_p (number-theoretic).
  - `Research/EulerSeq.lean` — e (transcendental, Σ 1/k!).
  - `Research/WallisSeq.lean` — π/2 (transcendental, Wallis product).

All under the falsifiability rule of `AXIOM.md` §5.2.1: if any
result truly required an additional axiom, the entire theory
would be discarded.

## Documentation

| File | Purpose |
|------|---------|
| `AXIOM.md` | Seed axiom + falsifiability contract. |
| `ORIGIN.md` | Original prompt chain (frozen 2026-04-24). |
| `CLAUDE.md` | Session operating manual + organization rules. |
| `NOTATION.md` | Notation conventions (no ZFC artifacts). |
| `IMPLEMENTATION.md` | Raw + Firmware Lean implementation audit. |
| `AUDIT_Lean.md` | Lean × AXIOM correspondence audit. |
| `PAPER1_OUTLINE.md` | Paper 1 structure + argument flow. |
| **`ANALYSIS213.md`** | **★ 분석학 213 — 학부 1학년 미적분 + ODE + Newton + 7 초월함수 종합 paper.** |
| **`CATALOG213.md`** | **★ Library reference — import 경로 + 정리 카탈로그 + usage examples.** |
| `research/infinity-as-lens/` | Detailed notes (numbered narrative). |
| `research/r5-critique/` | Sub-track: ℝ-algebra assumption critique (Paper 2 candidate). |
| `framework/E213/` | Lean 4 formalization. |
| **`framework/E213/Math/Analysis213.lean`** | **★ 라이브러리 entry point — single import for all analysis results.** |

## Lean architecture (`framework/E213/`)

```
E213/
├── Firmware/        — Raw axiom (canonical-form subtype, Internal namespace)
├── Hypervisor/      — Lens framework (view, equiv, refines)
├── OS/              — Pigeonhole, arity forcing, primitives
├── App/             — Applications (Simplex)
├── Meta/            — Lens catalogue, typeclass hierarchies
├── Tactic/          — Custom macros (quad_norm, hurwitz_ring, …)
├── Infinity/        — Cantor / Countable / Tower / Pair
└── Research/        — Demonstration suite + framework + catalogue
    └── CayleyDickson/ — R5-critique sub-track (Paper 2 candidate)
```

**Layering rule.** Each layer imports only the public API of layers
below it.  Firmware confines `Tree` to `E213.Firmware.Internal`;
consumers see `Raw`, smart constructors, `Raw.fold`, `Raw.rec`.

## Build

```
cd framework
lake build
```

Lean 4 core only — no Mathlib.  All 90+ Research modules build
clean.  `#print axioms` for every public theorem returns at most
`[propext, Quot.sound]`.

## Author & licence

- Author: **Mingu Jeong** only.  Claude (Anthropic) in Acknowledgments.
- 0 sorry, 0 external axioms beyond Lean 4 core baseline.

---

*"The axiom is not a choice but a residue — what cannot be
avoided when one tries to point at anything at all."*
