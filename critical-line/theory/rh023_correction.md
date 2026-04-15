# RH_023 Correction: Rank Effect, Not Representation Theory

## Controlled Test (inline, 2026-04-14)

Same rank, different representation type:

```
=== rank 3 ===
ℂ³ (complex rep):           96% on circle
ℂ³⊕ℂ³ σ-sym (self-conj):  96% on circle  ← SAME

=== rank 5 ===
ℂ⁵ (complex rep):           96% on circle
ℂ⁵⊕ℂ⁵ σ-sym (self-conj):  96% on circle  ← SAME
```

## Conclusion

The 96% vs 39% in RH_023 Test 2 was driven by **rank difference** (5 vs 2),
not by complex vs self-conjugate representations.

When controlling for rank and norm, both representation types give
identical Ihara Ramanujan fractions (96%).

The "Artin decomposition" interpretation was **incorrect**.
The Jarlskog suppression (J_t/J_c = 0.41) IS real, but it doesn't
translate to Ihara zero locations.

## What Remains True
- G = G_c + G_t (trace decomposition) ✓
- Tr(G_c)/N = 5/d_ind ✓
- σ-symmetrization reduces rank (Theorem 2) ✓
- σ-symmetrization suppresses Jarlskog (Theorem 2) ✓
- Ihara Ramanujan depends on rank/N ratio, not rep type ← NEW

## What Was Wrong
- "Complex reps → zeros on circle, self-conj → zeros off" ✗
- The rank reduction from σ caused the apparent split ✗
