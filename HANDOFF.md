# Session Handoff — 2026-04-27 (Cohomology Marathon Planned)

## Branch
`claude/review-paper-directory-nDw9L` (committed + pushed this session).

## What Was Done This Session

### 1. Open Problem #1 progress (1/α_em)
- `BaselBoundTight.lean` — two-sided telescoping bracket
  S(N)+1/(N+1) ≤ ζ(2) ≤ S(N)+1/N. Width 1/(N(N+1)).
- `AlphaEM137Tight.lean` — bracket on candidate at N=20 has width
  0.14 (vs N=10 width 6.0 baseline; 43× tighter).
- `AlphaEMStructuralGap.lean` — 5.443×10⁻⁴ gap to observed
  documented as first-class falsifier target. All 0-axiom.

### 2. "What is α_em from Raw under lensing" — answered
Re-reading the existing chain (`PhotonKernel`, `FaceTerms`,
`AlphaEMSimplicial`, `AlphaEMUnified`, `AlphaEMDerivation`) reveals:

**1/α_em(IR) = unique graded simplicial-cohomology sum on
K_{NS,NT}^{(c)} ⊂ Δ⁴ at atomicity (3, 2, 2, 5).** Five terms, all
atomicity-forced geometric invariants. Already proven 0-axiom.

Critical correction: the "conjectural d²/NS = 25/3" tag in
`AlphaEM137.lean` was wrong. `AlphaEMUnified.lean` already proves
25/3 = (NS²−1) + 1/NS = b₁ + 1/(#4-cycles) — both simplicial
quantities derived from Raw. Not ad hoc.

The 5.4×10⁻⁴ gap is the residual between the five-term simplicial
sum and observed 137.036. Most likely missing: a sixth simplicial
invariant (H², cup product, or higher cell-complex term).

### 3. Cohomology 213 marathon planned
- `blueprints/math/15_cohomology_213.md` — base spec
- `blueprints/math/15_cohomology_213_phases.md` — CA→CF phases
- `blueprints/math/INDEX.md` updated (field 15 added)
- `blueprints/INDEX.md` updated (cohomology = next math priority)
- `guide/14_cohomological_calculus.md` updated
- `guide/INDEX.md`, `guide/STATUS.md` updated

Marathon target dir: `lean/E213/Math/Cohomology/`. Six phases:
CA cochain + δ²=0, CB Hodge ⋆, CC Betti numbers, CD cup product,
CE α_em sixth-term hunt, CF capstone.

## Open Problems (priority order)

### 1. Cohomology 213 marathon — **Phases CA + CB closed**
8 files / ~25 theorems / 0 axiom in `lean/E213/Math/Cohomology/`:
Cochain + SimplexBasis + Delta + DeltaSqZero + TrivialCases (CA);
HodgeStar + HodgeInvolution + HodgeDelta (CB).

Phase CB: ⋆: Cᵏ → Cⁿ⁻ᵏ via set-theoretic complement;
⋆⋆ = id verified on multiple Bool-pure cochains; codifferential
`codiff = ⋆δ⋆` at (5,2) and (5,3) decide-checked.

**Lessons (CB):** cochains using `fun i => i.val = 0` (Prop)
trigger elaboration errors when chained through `hodgeStar`
(Nat-sub in result type). Use Bool-pure (`==`).
`hodgeStar n k m σ` needs all three (n, k, m) explicit.

**Phase CC next:** Betti numbers on Δ⁴ and K_{3,2}^{(2)}.
**b₂(K_{3,2}^{(2)})** is the α_em 5.4×10⁻⁴ candidate.

### 2. Phase CC b₂(K_{3,2}^{(2)}) — direct physics payoff
Compute b₂ at cochain level. If non-trivial, candidate sixth
simplicial invariant for the α_em gap.

### 3. Real213 Phase B–H (cohomological calculus extension)
General `cutMul` propEq remains the wall.

### 4. T3 chapters → T2/T1 migration
ℂ uniqueness (Frobenius → Raw-internal) is highest-leverage.

### 5. Single-theorem AxiomMinimality
Tighten `Meta/AxiomMinimality.lean`.

## File Map

```
lean/E213/Physics/BaselBoundTight.lean        ← α_em 1a
lean/E213/Physics/AlphaEM137Tight.lean        ← α_em 1a
lean/E213/Physics/AlphaEMStructuralGap.lean   ← α_em 1b documented
blueprints/math/15_cohomology_213{,_phases}.md ← marathon plan
guide/14_cohomological_calculus.md, INDEX, STATUS ← updated
```

## Authors

- Mingu Jeong (Independent Researcher) — theory originator.
- Claude (Anthropic): formalization + planning — Acknowledgments.
