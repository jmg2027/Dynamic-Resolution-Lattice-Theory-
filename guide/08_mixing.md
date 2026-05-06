# 08 — Mixing (CKM, PMNS)

**Tier:** T2
**Status:** Partial — Cabibbo angle and sin²θ₁₃ match; full PMNS open.
**Lean:** `Physics/Mixing/CabibboAngle.lean`, `Physics/Mixing/CKMHierarchy.lean`,
`Physics/Mixing/NeutrinoMixing.lean`, `Physics/Mixing/CPViolation.lean`.

## Best current statement

CKM and PMNS mixing matrices are not free; their entries are forced
by the chiral atomic decomposition (Ch. 02) acting on the generation
structure (Ch. 02 Discovery — 3 generations from C(5,2) modulo
diagonal).

### Cabibbo angle (4/27 close to passing)

```
λ_C = sin θ_C = 5/22
λ_C² = 25/484 ≈ 0.05165
```

Observed λ_C ≈ 0.2243, λ_C² ≈ 0.0503. `CabibboAngle.lean` proves
λ_C² < 1/4 by `decide`. Falsifier candidate: any LHCb / Belle II
refinement outside the bracket → discard.

### Neutrino sector

```
sin² θ₁₃ = 0.0220   (DRLT)   vs 0.0220 (observed)   −0.07σ
m₃ / m₂ = 5.712     (DRLT)   vs 5.71  (observed)    +0.04%
```

Both closed to ppm level; both passing 4/27 standard. JUNO (~2030) will
test mass ordering — falsifier on the table.

### CP violation

`CPViolation.lean` derives δ_CKM ≈ 1196 mrad with bracket width 200
mrad. Passing 4/27 standard at sub-percent.

## 213 sharpening

- "Why three generations" → answer (Discovery): C(5,2) = 10 pairs
  reduce to 3 channels modulo diagonal absorption at d = 5.
- "Why Cabibbo λ ≈ 0.22" → answer: rational 5/22 at the leading order;
  no Yukawa fit.
- "Why neutrino mixing is large but quark mixing is small" → answer:
  chiral atomic decomposition acts differently on +2/3, −1/3 quark
  charges vs neutral leptons. Narrative; not yet single Lean theorem.

## Open / next

- Full PMNS matrix in one Lean theorem (currently per-angle).
- Tighten Cabibbo λ from bracket-only to ppm closure.
- Predict δ_CP for neutrinos — currently informal extrapolation from
  CP-CKM closed result.
- Connect mixing structure to mass spectrum (Ch. 06) in a single
  theorem rather than parallel derivations.

## Sources

- `papers/paper3_zero_parameter_predictions.tex` (mixing entries)
- `papers/drlt-book/chapters/ch11_mixing.tex`
- `lean/E213/Physics/Mixing/CabibboAngle.lean`, `CKMHierarchy.lean`,
  `NeutrinoMixing.lean`, `CPViolation.lean`.
- `seed/AXIOM/04_falsifiability.md` § 4–5 (PMNS, Cabibbo).
