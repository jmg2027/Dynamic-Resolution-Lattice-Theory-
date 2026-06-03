# G185 — the linear-algebra program for the general Hadamard product

**Date**: 2026-06-03.  **Status**: foundation started (Phase A, the `n×n` determinant).
The last open ring operation of `theory/math/analysis/cfinite_orbit_dimension.md`:
`CFiniteZ s → CFiniteZ t → CFiniteZ (s·t)` (pointwise/Hadamard product).  Geometric
factors are done (`CFiniteRing.cfiniteZ_geomScale`, `cⁿ·s`); the general case is here.

## The mathematics (why it is heavy)

`s` C-finite of order `k`, `t` of order `m`.  The `km` products `u_{pq}(n) = s(n+p)·t(n+q)`
(`p<k`, `q<m`) are closed under the shift `E`: `E u_{pq} = u_{p+1,q+1}`, reducing
`s(n+k) = Σ aᵢ s(n+i)` and `t(n+m) = Σ bⱼ t(n+j)` at the boundary.  So the vector
`V(n) = (u_{pq}(n))` satisfies `V(n+1) = M·V(n)` for a fixed `km×km` integer matrix `M`
(a Kronecker product of the two companion matrices), and `s·t = V₀₀ = first component`.

**The crux — monic.**  `CFiniteZ` requires a *monic* `ℤ`-recurrence.  Plain linear
dependence of the `km+1` vectors `V(0),…,V(km)` gives only a *non-monic* relation
`Σ cᵢ V(i)=0` (leading `c_K` need not be `±1` over `ℤ`).  The monic integer annihilator is
the **characteristic polynomial** `χ_M(z) = det(zI − M)` (monic, integer, degree `km`), and
**Cayley–Hamilton** `χ_M(M)=0` gives `Σ (χ_M)ᵢ V(i)=0` with leading coefficient `1` — whence
the first component yields the monic recurrence for `s·t`.  Equivalently `χ_M` is the
**resultant** (Sylvester determinant) of the two characteristic polynomials, with roots
`{αᵢβⱼ}`.  Either route needs `det` of an `n×n` integer matrix.

There is *no* shortcut to monic over `ℤ` without the determinant: the minimal polynomial of
`M` on `V(0)` is monic only over `ℚ` (rational coefficients); integrality comes from `χ_M`
being an integer monic polynomial (Gauss), which is exactly `det(zI−M)`.

## Repo survey (what exists / the gaps)

Done by a read-only sweep of `lean/E213/Lib/Math/`.

  - **Exists**: `Linalg213/` (the home — `Vector` ℕ-valued `Fin`-indexed, `Rank` bounded
    linear-independence, `Span`, `Gram`, `Gap/Determinant` **2×2/3×3 only**,
    `Gap/MatrixMul` ℕ bounded).  Casoratian/Wronskian 2-term determinant identities
    (`CassiniUnimodular`, `Cauchy/Casoratian{Step,Signed}`).  `Mobius213/Px/FibonacciAtomicLock`
    (concrete 2×2 `Q`-matrix, `P=Q²`).  Finite sums `bsum` (`NewtonGregory`), `shiftSum`/`linComb`
    (`CFiniteRing`).  `Meta/Int213` ring (`ring_intZ`), `powInt`.
  - **Gaps (to build)**: ❌ `n×n` determinant, ❌ multilinearity / alternating / Laplace
    expansion properties, ❌ characteristic polynomial, ❌ Cayley–Hamilton, ❌ adjugate, ❌
    companion matrix, ❌ resultant / Sylvester, ❌ "`N+1` vectors in `ℤ^N` are dependent".

## Phased build plan

  - **Phase A — `n×n` determinant over `ℤ`** (`Linalg213/DetN.lean`, **started**).  Cofactor
    (first-row Laplace) expansion: `altSign`, `minor`, `cofSum`, `det`.  Sanity `det_one`,
    `det_two`.  **Next**: multilinearity in the first row, the **alternating** property
    (two equal rows ⟹ `det=0`) — the key lemma, and the hard induction (sign bookkeeping).
  - **Phase B — characteristic polynomial + adjugate**.  `charPoly M z = det(zI−M)` (monic,
    integer); the adjugate `adj` and the identity `M·adj M = det M · I`.
  - **Phase C — Cayley–Hamilton** for integer matrices (`χ_M(M)=0`), via the adjugate
    identity.  (Or the targeted resultant route.)
  - **Phase D — companion/Kronecker matrix `M` for the Hadamard** (`Cauchy/CFiniteHadamard.lean`):
    build `M` from `a,b`, prove `V(n+1)=M·V(n)`, apply CH, extract the first-component monic
    recurrence ⟹ `cfiniteZ_mul`.

This also unlocks **C-B** (Casoratian rank = orbit dimension): the same `det` + a Hankel/
Casoratian determinant argument.

## Honest scope

This is a ~1000+ line, multi-session foundation.  Phase A (the determinant + its alternating
property) is itself a substantial sub-build; Cayley–Hamilton (Phase C) is a genuine theorem.
Each phase is independently reusable (`Linalg213` general linear algebra), so bank phase by
phase.  Current: Phase A definition + sanity committed (`DetN`, 6 PURE).

## Anchors

  - Target: `theory/math/analysis/cfinite_orbit_dimension.md` "Open frontier" (the general
    Hadamard bullet) + `Cauchy/CFiniteRing.cfiniteZ_geomScale` (the geometric-factor corner).
  - New: `lean/E213/Lib/Math/Linalg213/DetN.lean`.
