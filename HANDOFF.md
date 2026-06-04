# Session Handoff — 2026-06-04 (★★★ C-finite Hadamard product CLOSED via integer Cayley–Hamilton)

## Branch
`claude/goal-g183-CxU4X` (develop here; merged to `main` earlier this branch).  Full
`cd lean && lake build` clean; every new theorem ∅-axiom (`tools/scan_axioms.py` → `N pure / 0 dirty`).

## ★★★ Headline: the G185 program is COMPLETE

`CFiniteZ s → CFiniteZ t → CFiniteZ (s·t)` — the C-finite **Hadamard (pointwise) product** — is
**proven, ∅-axiom** (`Cauchy/CFiniteHadamard.cfiniteZ_mul`), the last open ring operation of the
C-finite sequences.  Built end-to-end this branch with no Mathlib, no `sorry`, no axioms:

| Module | PURE | Role |
|---|---|---|
| `Linalg213/Permutation` | 33 | Leibniz determinant + sign theory |
| `Linalg213/PermClosure` | 76 | symmetric group, **alternating**, multilinear, degeneracy |
| `Linalg213/Laplace` | 53 | cofactor expansion + **adjugate identity** `M·adj M = det M·I` |
| `Linalg213/CayleyHamilton` | 27 | the **matrix ring** (assoc, identity, distributivity, powers, sums) |
| `Lib/Math/PolyZ` | 47 | integer polynomials + **uniqueness** + degree bound |
| `Linalg213/PolyDet` | 20 | polynomial determinant, **char poly**, monicity |
| `Linalg213/CharPolyAdj` | 31 | **integer Cayley–Hamilton** `χ_M(M)=0` + the recurrence bridge |
| `Cauchy/CFiniteHadamard` | 21 | flat↔grid `divmod`, Kronecker companion, **`cfiniteZ_mul`** |

### The arc
adjugate identity `M·adj M = det M·I` → lift to `ℤ[X]` via `coeff_unique` (polynomial uniqueness) →
coefficient relations + degree bound → **telescoping** ⟹ `χ_M(M)=0` → the **recurrence bridge**
(`w(n+1)=M·w(n)` ⟹ each component obeys the monic χ_M recurrence) → the **Kronecker companion** for
the product vector `w(n)_{(a,b)}=s(n+a)t(n+b)` (factored `Mmat=Ms·Mt`; `vecRec`) → `cfiniteZ_mul` via
`charPoly_monic` + `cfiniteZ_of_shiftRec`.  The flat↔grid bijection was a fresh ∅-axiom
**fuel-structural `divmod`** (core `Nat./`/`%` are propext/Quot-dirty).

## Next
- **Promotion**: the `Linalg213` determinant + Cayley–Hamilton sub-tree is closed and a candidate for
  `theory/` narrative promotion (`theory/PROMOTION_CRITERIA.md`).
- `cfiniteZ_mul` closes the C-finite ring frontier in
  `theory/math/analysis/cfinite_orbit_dimension.md` ("Open frontier" → done) — update that narrative.
- Unlocked: **C-B** (Casoratian rank = orbit dimension) reuses the same determinant theory.

## DRLT Validation Standard
Still the repo's stated real target (untouched): ppb-ppm precision theorem and/or a strict
∅-axiom falsifier (`N_gen=3`, `θ_QCD`).
