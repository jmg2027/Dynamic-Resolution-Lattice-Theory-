# Topology 213 — Module Index

Blueprint: `blueprints/math/03_topology_213.md` (retired).

## Modules

| File | Topic | Theorems | Status |
|---|---|---|---|
| `DyadicOpen.lean` | open = `List DyadicBracket`; size additive under union; structurally finite | 10 | ∅-axiom |
| `Compactness.lean` | `IsCover` (membership); Heine-Borel = trivial (cover IS finite by `List`) | 7 | ∅-axiom |
| `Continuity.lean` | `IsContinuousModulus` structure; identity / constant / composition | 6 | ∅-axiom |
| `ContinuityArith.lean` | Continuity under arithmetic operations | 4 | ∅-axiom |
| `Connectedness.lean` | `adjacent` predicate; `Chain` finite-list adjacency; `chain_finite` | 7 | ∅-axiom |
| `EulerChi.lean` | χ(Δ⁴) = 1, χ(S³) = 0, χ(K_{3,2}^{(c=2)}) = −7; face count totals | 10 | ∅-axiom |
| `ModulusStructure.lean` | bare `IsModulusStructure` typeclass; 3-way bridge across `IsContinuousModulus` (Topology), `IsRicciModulus` (GeometrizationConjecture), `BracketCauchyModulus` (Analysis) | 12 | ∅-axiom |
| `Capstone.lean` | 5 cluster witnesses + `total_witness` | 6 | ∅-axiom |
| `Topology.lean` | umbrella | — | — |

**Total**: 62 atomic facts, all `#print axioms` ∅.

## 213-native paradigm parallel

  * **Open sets are countable by structure**: `List DyadicBracket`
    is a `List`, finite by construction.  No σ-algebra-style
    Choice issue.
  * **Heine-Borel is trivial**: every cover IS its finite subcover
    because covers are `List`s.  No completeness-of-ℝ argument.
  * **Continuity = `Nat → Nat` modulus**: same data as
    `IsSmooth.linearityModulus` in `Lib/Math/Analysis/`.  No real
    ε/δ.
  * **Connectedness = finite chain adjacency**: list-level, not
    arbitrary topological.
  * **Euler χ = atomic alternating sum** of `binom 5 k`.

## Connection to existing infrastructure

  * `Lib/Math/Analysis/DyadicSearch/DyadicBracket.lean` — bracket
    type.
  * `Lib/Math/Analysis/Differentiation/Smooth.lean` —
    `IsSmooth.linearityModulus` (continuity proper).
  * `Lib/Physics/Simplex/Counts.lean` — `binom`, face counts.
  * `Lib/Math/Cohomology/CutExpFiniteTruncation.lean` — Grade-N
    nilpotency (parallel structural truncation).

## Out of scope (separate continuation)

  * Tychonoff (product compactness with Choice — 213-native form
    needs cohomology lift).
  * Manifold-as-bracket-atlas formal definition.
  * Fundamental group / homotopy (would link to Logic 213's
    proof-as-trajectory).
