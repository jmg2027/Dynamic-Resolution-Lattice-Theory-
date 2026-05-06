# Cohomology 213 — Phase Plan (CA → CF)

Companion to `15_cohomology_213.md`. Six-phase marathon following
the Phase 1 Physics template. Each phase ≈ 4–8 commits, ~5–10 Lean
files, 80-line limit per file.

Target: `lean/E213/Lib/Math/Cohomology/`. Naming: `Cohomology<Topic>.lean`.

## Phase CA — Cochain Complex Foundation

| File | Theorem |
|---|---|
| `CohomologyCochain.lean` | `Cᵏ` type, `delta : Cᵏ → Cᵏ⁺¹` |
| `CohomologyDeltaSqZero.lean` | `delta ∘ delta = 0` (decide on Δ⁴) |
| `CohomologySimplexBasis.lean` | basis = `Fin (binom d k)` |
| `CohomologyTrivialCases.lean` | smoke tests at d = 2..5 |

Goal: cochain complex defined for arbitrary `Δᵈ`, δ²=0 by `decide`.

## Phase CB — Hodge Duality (lift to cochain level)

| File | Theorem |
|---|---|
| `CohomologyHodgeStar.lean` | ⋆: Cᵏ → Cᵈ⁻ᵏ defined |
| `CohomologyHodgeInvolution.lean` | `⋆⋆ = (-1)ᵏ⁽ᵈ⁻ᵏ⁾ id` |
| `CohomologyHodgeDelta.lean` | δ ↔ codifferential under ⋆ |

Goal: chain-level Hodge; specializes to `SimplexCounts.hodge_*`.

## Phase CC — Betti Numbers via Decide

| File | Theorem |
|---|---|
| `CohomologyBetti.lean` | `b k := dim ker δ_k − dim im δ_{k−1}` |
| `CohomologyBettiSimplex.lean` | b_k(Δᵈ) = δ_{k,0} (k=0..d) |
| `CohomologyBettiBipartite.lean` | b₀=1, b₁=8 of K_{3,2}^{(2)} re-proven |
| `CohomologyBettiHigher.lean` | **b₂(K_{3,2}^{(2)})** — α_em 6th-term candidate |

Goal: re-prove scalar Bettis at cochain level; compute higher.

## Phase CD — Cup Product

| File | Theorem |
|---|---|
| `CohomologyCup.lean` | `cup : Cᵏ ⊗ Cˡ → Cᵏ⁺ˡ`, bilinear |
| `CohomologyCupLeibniz.lean` | δ(α ⌣ β) = δα ⌣ β ± α ⌣ δβ |
| `CohomologyCupRing.lean` | H* ring structure |

Goal: ring on H*; cup product table for K_{3,2}^{(2)}.

## Phase CE — α_em Sixth-Term Hunt

| File | Theorem |
|---|---|
| `CohomologyAlphaEMHigher.lean` | H²(K_{3,2}^{(2)}) generators |
| `CohomologyAlphaEMCup.lean` | cup-product invariants |
| `CohomologyAlphaEMSixthTerm.lean` | candidate ≈ 5×10⁻⁴ invariant |

Goal: identify if α_em gap fits H² class or cup invariant; if not,
conclude "five-term is complete; gap is residual".

## Phase CF — Capstone

| File | Theorem |
|---|---|
| `CohomologyCapstone.lean` | α_em = Σ graded simplicial invariants |
| `CohomologyAlphaEMComplete.lean` | gap closed OR irreducible |

Goal: single capstone — full structural origin of 1/α_em, OR proof
that five-term is the maximal simplicial decomposition.

## Connections

Real213 (Ch. 14): generalize FluxCut to k-cochains.
Physics Ch. 03/05/12: face/cycle data input.
AlphaEMStructuralGap: Phase CE closes or sharpens the falsifier.
