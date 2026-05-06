# 05 — Coupling Constants

**Tier:** T2 (classical adequate; 213 sharpens individual brackets)
**Status:** Partial — α_GUT and α_em closed as rational brackets, not yet
to ppm width. Headline 1/α_em = 137.036 *not yet* 4/27-passing.
**Open Problem #1 status (2026-04-27 update):** split into 1a (bracket
tightening, computational) + 1b (5.4×10⁻⁴ structural gap, research).
**Lean:** `Physics/Couplings/AlphaGUT`, `AlphaEM`, `AlphaEM/V137`, `AlphaEM/V137Tight`,
`BaselBound`, `Basel/Bound` (BoundTight merged in 2026-05-05), `AlphaEMStructuralGap`.

## Best current statement

Classical: `α_GUT = 6/(25π²)`, `1/α_GUT = d²·ζ(2) ≈ 41.123`.

In 213, ζ(2) is replaced by rational bracket `[S(N), upper(N)]`
(`BaselBound.lean`). At N = 3:
`1/α_GUT ∈ [1225/36, 4575/108] ≈ [34.03, 42.36]` strictly contains
41 (`decide`, 0 axioms). Bracket tightens monotonically with N.

### α_em chain (candidate formula, honest-tagged)

```
1/α_em(bare) = 60·ζ(2) + 30                      (Weinberg sum)
1/α_em(IR)   = 60·ζ(2) + 30 + d²/NS + α_GUT/(NS+1)
             ≈ 137.0354548                       (asymptotic, perfect ζ)
```

At N=10 the candidate bracket contains 137 (`decide`).
The `d²/NS = 25/3` term is **conjectural structural form** — not yet
derived from the Raw axiom.

### α_3 (strong coupling, confined regime)

`PhotonKernel.lean`: 1/α_3 = NS²−1 = 8. Exact; depends on
Discovery 2 (photon = cycle space of K_{3,2}).

## 213 sharpening

- ζ(2) → S(N) rational bracket; transcendental replaced by finite
  rational interval. Width is the question, not the value.
- α_GUT three classical paths (simplex / RMT / coprimality) collapse
  into one bracket-tightening problem.
- 1/α_3 = 8 exact from atomicity — no classical-QCD counterpart.

## Open / next — Open Problem #1 split

**1a (computational, decide-checked).** `Basel/Bound` (BoundTight merged in 2026-05-05) adds the
two-sided telescoping bound: `S(N) + 1/(N+1) ≤ ζ(2) ≤ S(N) + 1/N`,
giving width `1/(N(N+1))` — quadratic improvement. `AlphaEM/V137Tight`
applies it: at N=20 the candidate-formula bracket has width 0.14
(vs 6.0 baseline at N=10, a 43× improvement). N=50 reaches width
0.024. N>50 hits Lean's default `maxRecDepth` for `S` unfolding.

**1b (structural research — newly first-class).** Even with a
zero-width Basel bracket, the candidate formula's asymptotic value
137.0354548 differs from observed 137.0359991 by **5.443×10⁻⁴**.
This gap is intrinsic to the formula. Bracket tightening alone
**cannot** close it.

`AlphaEMStructuralGap.lean` records the gap as a Lean-level rational
falsifier target with three candidate corrections:
- Next-order Dyson tail (α_GUT² term) — too small alone (~3.7×10⁻⁵).
- Refined d²/NS coefficient — derivation from Gram-channel atomicity
  is open.
- Hadronic-VP analog from d=5 atomic structure — unknown.

The **research target** is therefore: derive an explicit Raw-axiom
correction at the 5×10⁻⁴ scale, OR demonstrate that the candidate
formula is the wrong structural form for 1/α_em at the IR scale.

## Sources

- `papers/paper2_frobenius_to_gauge.tex` (α_GUT three paths)
- `papers/paper4_zeta_beta.tex` (coupling running)
- `papers/paper6_simplex_coupling.tex`
- `papers/drlt-book/chapters/ch08_couplings.tex`
- `lean/E213/Lib/Physics/Couplings/AlphaGUT.lean`, `AlphaEM/V137.lean`,
  `BaselBound.lean`, `PhotonKernel.lean`.
