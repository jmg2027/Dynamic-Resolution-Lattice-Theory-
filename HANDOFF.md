# Session Handoff — 2026-04-27 (Cohomology Marathon Phases CA+CB+CC partial)

## Branch
`claude/review-paper-directory-nDw9L` (committed + pushed).

## What Was Done

### 1. Open Problem #1 (1/α_em) — bracket tightening + structural gap
- `BaselBoundTight.lean` — two-sided telescoping, width 1/(N(N+1)).
- `AlphaEM137Tight.lean` — N=20 bracket width 0.14 (43× tighter).
- `AlphaEMStructuralGap.lean` — 5.443×10⁻⁴ gap as falsifier target.

### 2. "What is α_em from Raw under lensing" — answered
**1/α_em(IR) = unique graded simplicial-cohomology sum on
K_{NS,NT}^{(c)} ⊂ Δ⁴ at atomicity (3,2,2,5).** Five terms, all
atomicity-forced (already proven in `AlphaEMSimplicial.lean`).
"25/3 conjectural" tag was wrong: 25/3 = (NS²−1) + 1/NS = b₁ +
1/(#4-cycles), both Raw-derived.

### 3. Cohomology 213 marathon — Phases CA + CB + CC partial
9 files / ~28 theorems / 0 axiom in `lean/E213/Math/Cohomology/`.

CA (cochain foundation, 5 files): Cochain + SimplexBasis + Delta +
DeltaSqZero + TrivialCases. δ²=0 verified at concrete cochains.

CB (Hodge ⋆, 3 files): HodgeStar + HodgeInvolution + HodgeDelta.
⋆⋆ = id verified; codiff = ⋆δ⋆ defined at (5,2) and (5,3).

CC partial (1 file): BettiKernel.lean defines kernel enumeration.
`kerSizeDelta 5 0 = 1`, `kerSizeDelta 5 1 = 2` verified —
confirms Δ⁴ is contractible (b̃_0 = b̃_1 = 0 reduced ℤ/2).

## Lessons learned

1. **Prop coercion breaks `decide` through `hodgeStar`.**
   Cochains via `fun i => i.val = 0` (Prop) + `Decidable` autoconvert
   to Bool, but chained through `hodgeStar`'s Nat-sub result type
   triggers "expected type must not contain free variables".
   Use Bool-pure (`==`, `fun _ => true`).
2. **`hodgeStar n k m σ` needs all three (n,k,m) explicit.**
3. **`Nat.fold` doesn't reduce under `decide`.** Use
   `(List.range _).filter ... |>.length` for kernel enumeration.

## Open Problems (priority)

### 1. Phase CC continuation (α_em 6th-term payoff blocked)
K_{3,2}^{(2)} cohomology requires a SEPARATE cochain construction
(graph cochains, not simplicial-on-{0..n-1}).  And
b₂(K_{3,2}^{(2)}) = 0 trivially (1-dim graph), so the sixth term
— if it exists — must come from Phase CD (cup product) or a
2-cell extension.  Plan: skip to Phase CD next.

### 2. Phase CD — cup product
`Cohomology/Cup.lean` defines `cup : Cᵏ ⊗ Cˡ → Cᵏ⁺ˡ` (XOR
bilinear), Leibniz, ring on H*. Cup product invariants on
K_{3,2}^{(2)} are next α_em-gap candidate.

### 3. Real213 Phase B–H (cohomological calculus extension)
General `cutMul` propEq remains the wall.

### 4. T3 chapters → T2/T1 migration
ℂ uniqueness (Frobenius → Raw-internal) highest-leverage.

### 5. Single-theorem AxiomMinimality.

## File Map (this session)

```
lean/E213/Physics/{BaselBoundTight,AlphaEM137Tight,AlphaEMStructuralGap}.lean
lean/E213/Math/Cohomology/{Cochain,SimplexBasis,Delta,DeltaSqZero,
  TrivialCases,HodgeStar,HodgeInvolution,HodgeDelta,BettiKernel}.lean
blueprints/math/15_cohomology_213{,_phases}.md
guide/{14_cohomological_calculus,INDEX,STATUS}.md, papers/README.md
```

## Authors

- Mingu Jeong (Independent Researcher).
- Claude (Anthropic): formalization + planning.
