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

## The number-tower reframing (the native direction)

Recognizing the `Lens/Number` **number-tower founding** thread (on `main`:
`DifferenceLensFounding` ℤ, `RatioLensFounding` ℚ, `PairCompletion`, `NatPairToQPos`,
`book/foundations`) recasts this whole program:

  - **`+`-closure and Hadamard `⊙`-closure are the ℤ/ℚ sibling duality.**  `conv` (sum-closure)
    multiplies char polys → roots are the **union** `α ∪ β` (additive/count reading = the ℤ rung,
    `DifferenceLensFounding`).  Hadamard needs the **composed product** → roots are the pairwise
    **product** `{αᵢβⱼ}` (multiplicative/ratio reading = the ℚ rung, `RatioLensFounding`).
    `PairCompletion` already proves "invert is one move" — one mechanism (pair + diagonal-quotient
    + swap) read at `+` (ℤ, swap = negation) and `·` (ℚ, swap = reciprocal).  So `+`/`⊙` on
    C-finite are that same invert-move read on two operations; `⊙` is the multiplicative twin of
    `conv`, not a foreign object.

  - **The monic obstruction = the shared unit `det P = NS−NT = 1`.**  `RatioLensFounding`:
    ℚ's lowest-terms (coprimality) *is* the unimodular `det P = 1`, shared with ℤ
    (`SharedUnitAcrossReadings.the_unit_is_one_across_readings`).  My "monic = leading coeff a
    unit" requirement is the same condition; monic-ness of the resultant is the **unit preserved
    across the multiplicative reading**.  Concretely: the Fibonacci witness `cfiniteZ_fib`'s Cassini
    `fib(n+2)fib(n)−fib(n+1)² = ±1` *is* `PnFibonacciUniversal.det_pn_universal` (`det Qⁿ = unit`) —
    the same object.

  - **C-finite = the ratio rung of a sequence-tower** parallel to `ℕ→ℤ→ℚ→ℝ`: polynomial
    (Δ-nilpotent = count/ℤ rung) ⊊ C-finite (rational generating function `A(x)/Q(x)` = ratio/ℚ
    rung) ⊊ holonomic ⊊ … with non-holonomic π = the resolution/residue diagonal (the "runs upward
    without end" of `book/foundations/02`).  "Closed under an operation" = `book`'s
    **completeness-as-fixpoint** ("the operation returns its own codomain"); Hadamard closure makes
    C-finite a fixpoint under `⊙` too.

  - **`E = I + Δ` is the same one-move bundling.**  The dual operator algebras
    (`applyOp`/`applyShift`, `ePow=[1,1]ⁿ` / `dPow=[-1,1]ⁿ`) bundle `Δ = E − I` by one move — the
    `PairCompletion` mechanism, independently rediscovered at the operator level.

### Native redirect for the determinant-free composed product

The multiplicative twin of `conv` ("`mconv`", roots → pairwise products) should be built
*foundationally*, not by importing a Sylvester determinant.  Candidate route (being designed in the
companion note): **power sums multiply** — `pₗ(αβ) = pₗ(α)·pₗ(β)` — with Newton's identities
converting coeffs ↔ power sums.  The cross-check that `conv` ↔ power-sums-**add** confirms the
`+`/`⊙` = additive/multiplicative duality at the power-sum level.  Open feasibility: the Newton
`÷k` step over `ℤ` (∅-axiom integrality).  If `mconv` lands division-free, it is the genuinely
native Hadamard annihilator and likely sidesteps the full `n×n` determinant.  `DetN` remains the
fallback (resultant) and is independently needed for C-B (Casoratian rank).

**Integration TODO** (needs merging `main`'s founding thread into this branch): wire
`det_pn_universal` / `ns_minus_nt_is_one` to state "monic = shared unit" as a theorem; extend the
`book`/chapter with the C-finite ratio-rung as a parallel bundling chain.


## Update — mconv verdict (G188) + the explicit-spectrum corner (DONE)

The `mconv` power-sum/Newton route was designed (`research-notes/G188`) and found **not
∅-axiom-viable over ℤ**: the Newton `÷k` exactness is *always true* (composed product is
monic-integer, power sums are integer traces) but proving it ∅-axiom *is* the integral
symmetric-function theorem (multi-hundred lines, no `Int` exact-division layer, ℤ is the
difference-Lens not a quotient).  Structural root cause confirmed: a **monic** `ℤ` annihilator
provably needs the characteristic polynomial = a determinant; power sums / finite-orbit
dependence give only non-monic — the power-sum route is "the determinant in disguise".

**Banked instead (the cheap corner, ∅-axiom, no determinant)**: `CFiniteRing.cfiniteZ_geomCombo_mul`
— `(Σ aᵢ cᵢⁿ)·t` is C-finite for every C-finite `t` (one factor split / explicit integer spectrum),
via `cfiniteZ_geomScale` + `cfiniteZ_add`.  The general (both-non-split) case stays the determinant
program (Phase B/C: `DetN` → integer Cayley–Hamilton → Kronecker `M`), which also unlocks C-B.

## Update — DetN Phase B (multilinearity) + the alternating hard core

`Linalg213/DetN` extended to **13 PURE** (Phase B partial):
- `det_congr` — `det` respects *pointwise* matrix equality.  Crucial: `funext` is
  `Quot.sound`-dirty, so all matrix-as-function reasoning must go through pointwise congruence,
  not function equality.  This is the ∅-axiom matrix-work pattern.
- `setRow0`/`detMinor_setRow0` (the cofactor is row-0-independent), `det_row0_add`/`det_row0_smul`
  — `det` is a linear functional of the first row.

**The alternating property is the irreducible hard core.**  Two equal rows ⟹ `det = 0` (equivalently
antisymmetry under a row swap) does NOT decompose into easy pieces for a first-row cofactor `det`:
- Equal rows *both ≥ 1* (away from row 0): the minors inherit the equal pair — but when the pair is
  rows 1,2 the minor's pair is at positions 0,1, i.e. the *position-0* case again.
- The **row-0 ↔ row-1 swap** is genuinely not reducible to first-row expansion; the standard proof
  is a **double cofactor expansion** with `2×2` sub-minor sign bookkeeping (~200+ lines, ∅-axiom,
  no `funext`).  This is the one hard theorem gating linear-dependence (the `(−1)ʲ`-minor
  construction needs "repeated row ⟹ 0") and Cayley–Hamilton (the adjugate identity).

So the determinant program's remaining cost is concentrated in this single hard lemma; everything
downstream (linear dependence, char poly monic, CH, Kronecker `M`, `cfiniteZ_mul`) is gated by it.
Alternative: the permutation/parity determinant (alternating = parity-flip = the count-Lens
negation) makes alternating clean but needs a permutations+sign ∅-axiom build instead.
