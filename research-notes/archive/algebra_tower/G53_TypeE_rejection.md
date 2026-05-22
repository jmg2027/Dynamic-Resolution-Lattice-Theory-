# G53: Type E rejection — ℤ-base 4-row matrix completeness

## Question

Is there a Type E in our 213 algebra tower 4-row matrix? E.g.,
icosian quaternions (120 units, 2I binary icosahedral), Q(ζ_8)
(8 units), etc. — would they form a 5th row?

## Answer

**No.** The 4-row matrix (Type A/B/C/D) is exhaustive over ℤ-base
finite-unit rings with CD-doubling structure.

## The argument (Dirichlet unit theorem)

For a number field K = ℚ(α) with degree n = r₁ + 2r₂ (r₁ real
embeddings, r₂ complex pairs), the unit group of its ring of
integers O_K is:

    O_K^× ≅ μ(K) × ℤ^(r₁ + r₂ − 1)

Finite unit group requires r₁ + r₂ − 1 = 0, i.e., r₁ + r₂ = 1.

Two cases:
- (r₁, r₂) = (1, 0): K = ℚ itself (degree 1) → units {±1}, 2 elements
- (r₁, r₂) = (0, 1): K = imaginary quadratic field (degree 2)

For imaginary quadratic K = ℚ(√−d), unit group classification:

| d            | unit group | size | Type        |
|--------------|------------|------|-------------|
| d = 1        | μ_4        | 4    | A (ZI)      |
| d = 3        | μ_6        | 6    | C (ZOmega)  |
| d ≥ 2, d≠3   | μ_2        | 2    | B (ZSqrt)   |

That's exhaustive for *commutative* finite-unit base rings.

## Quaternion orders (non-commutative bases)

For non-commutative orders in quaternion algebras over ℚ, finite-unit
classification:

| order                    | unit group | size | Type |
|--------------------------|------------|------|------|
| Lipschitz ℤ⟨i, j, k⟩    | Q_8        | 8    | (= Type A's L3, doubled ZI) |
| Hurwitz ℤ⟨i, j, k, η⟩    | 2T         | 24   | **D**                       |

Lipschitz is NOT a separate Type; it equals Type A's L3 (since
CD-doubling ZI gives Lipschitz). So no new row.

## Why no Type E?

**Q(ζ_5) candidates** (icosian quaternions, 120 units):
- Q(ζ_5) has degree 4 over ℚ (since φ(5) = 4)
- Units form INFINITE group (Pell-type, from real subfield ℚ(√5))
- Icosian quaternion order has 120 finite units, BUT lives over
  ℚ(√5), NOT over ℚ
- Coefficient ring is ℤ[(1+√5)/2], not ℤ
- Outside our "ℤ-base" framework

**Higher cyclotomic Q(ζ_n) for n ∉ {1, 2, 3, 4, 6}**:
- φ(n) ≥ 4 for n ∈ {5, 7, 8, 9, 10, 11, ...}
- Degree-4+ extensions have infinite unit group (Pell-style)
- No finite-unit base ring

**Higher quaternion orders over larger number fields**:
- Same issue: coefficient ring no longer ℤ
- Outside framework

## Conclusion

Within "ℤ-base ring with finite unit group + CD-doubling structure",
the complete classification is exactly:

| Type | Base                  | Units | Group |
|------|-----------------------|-------|-------|
| A    | ZI = ℤ[i]              | 4     | Z_4   |
| B    | ZSqrt[-D] for D ≥ 2    | 2     | Z_2   |
| C    | ZOmega = ℤ[ω]         | 6     | Z_6   |
| D    | Hurwitz quaternion order | 24  | 2T    |

The 4-row matrix is **complete and bounded by Dirichlet's unit
theorem**. No Type E exists in this framework.

## 213-internal status

The 4 Types are each formally accessible at Lean ∅-axiom level:
- A: existing ZI/Cayley/Sedenion + LipschitzOrder4Monopoly etc.
- B: ZSqrtMinus2 tower (L3T-L6T) + Order4Monopoly_L*T
- C: ZOmegaDouble/Quad/Oct + Order distribution proofs
- D: Hurwitz213 (24 units, 2T binary tetrahedral)

Universal Order Growth law (UniversalOrderGrowth + UniversalOrderGrowthC)
covers all measured layer pairs.

## See also

- `lean/E213/Lib/Math/CayleyDickson/AlgebraTowerCapstone.lean` — bundle
- `research-notes/G56_session_summary_algebra_tower.md` — narrative
- `research-notes/G58_algebra_tower_completion.md` — final summary
