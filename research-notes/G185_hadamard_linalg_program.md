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

## Update — §3 column-skip commutation banked + the integration loop closed (18+3 PURE)

`Linalg213/DetN` → **18 PURE** (added §3); new bridge `Linalg213/FibCassiniDet` → **3 PURE**.

**Banked (the geometric core of alternating):**
- `colShift j l = if l < j then l else l+1` factored out of `minor`; `colShift_lt`/`colShift_ge`.
- ★ `colShift_comm {a ≤ c} : colShift a ∘ colShift c = colShift (c+1) ∘ colShift a` — deleting
  two columns in either order is the same.  Proven ∅-axiom by `Nat.lt_or_ge` case-splits +
  clean core ordering lemmas (`Nat.lt_of_lt_of_le`, `Nat.lt_irrefl`, `Nat.succ_lt_succ`, …, all
  PURE per `Pigeonhole`).  No propext.
- `detMinorMinor_comm {a ≤ c} : det n (minor (minor M a) c) = det n (minor (minor M (c+1)) a)` —
  lifts it to the double minor's determinant, pointwise via `det_congr`.

**Integration loop closed (the "monic = shared unit" 아하, concretely):** `FibCassiniDet`:
- `fibCas n i j = fibZ (n+i+j)` (the `2×2` companion power `Qⁿ` window).
- `cassini_fibZ_eq_altSign : fibₙ·fibₙ₊₂ − fibₙ₊₁² = altSign (n+1) = (−1)ⁿ⁺¹` (closed form, via
  `cassini_fibZ_zero` + `cassini_fibZ_step`).
- ★ `fibCas_det_eq_unit : det 2 (fibCas n) = (−1)ⁿ⁺¹` — the general determinant's `2×2` base
  **is** the orbit's conserved unit, the same unimodular `det = ±1` as the founding's shared unit
  (`PnFibonacciUniversal.det_pn_universal`, `det Qⁿ = unit`).  DetN validated against real content.

### The precise remaining gap (walk-in for the next session)

The whole alternating property reduces to ONE base case, then clean inductions:

1. **Base (hard):** *top two rows equal ⟹ `det (n+2) M = 0`.*  Double-expand: `det = Σⱼ Σₖ
   (−1)^{j+k} M₀ⱼ · M₀,(colShift j k) · det n (minor (minor M j) k)` (using row0=row1).  The
   involution pairing two distinct columns `a<b`: term `(j=a, k=b−1)` ↔ term `(j=b, k=a)` — by
   `detMinorMinor_comm` they share the double minor; `altSign` ratio is `−1` (since `b = (b−1)+1`);
   the row-0 scalars `M₀ₐM₀ᵦ = M₀ᵦM₀ₐ` are equal ⟹ the pair **cancels**.  Every term pairs (no
   self-fixed point, `colShift j k ≠ j`), so the sum is `0`.  *Obstacle*: reorganizing the
   **nested recursive `cofSum`** by this `(a,b−1)↔(b,a)` involution — there is no `Finset`/Fubini
   infra here, so a small "sum-over-nested-ranges with a sign-reversing involution ⟹ 0" lemma
   must be built first (the genuine remaining work; `colShift_comm`/`detMinorMinor_comm` are its
   per-term inputs, now ready).
2. **Multilinearity in any row `r`** (have it for `r=0`): expand along row 0, `M`'s row `r`
   becomes the minor's row `r−1`; induct.  Clean.
3. **Adjacent-rows-equal ⟹ 0, any position `i`**: expand along row 0 for `i≥1` (minor has the
   pair at `i−1`); base `i=0` is (1).  Clean.
4. **Adjacent-swap antisymmetry**: from (2)+(3) via `det(…,rᵢ+rᵢ₊₁,rᵢ+rᵢ₊₁,…)=0`.  Clean.
5. **Any two equal rows ⟹ 0**: move one row adjacent by (4)'s swaps; sign-only, lands on (3).

So the single irreducible build is the **nested-sum sign-reversing-involution ⟹ 0** lemma feeding
base (1); everything else is the clean induction ladder above.  This is the recommended next unit
(self-contained, reusable).  The permutation/parity determinant remains the alternative (alternating
= `sign(σ∘τ)=−sign σ`, also a list-involution reindex — same class of obstacle, plus a sign-by-
inversion-count build).

## Update — route chosen: permutation/Leibniz (essay-pinned); cornerstones banked

The intuition "det = Lens-quotient characteristic; det=0 = collapse of distinguishing" was pinned
as `theory/essays/determinant_as_quotient_characteristic.md`, which argues alternating's **natural
home is antisymmetrization** (`sign(σ∘τ)=−sign σ`), not the cofactor involution.  Route A is now
underway in `Linalg213/Permutation.lean` (**12 PURE**):

- **§1 (cornerstone)** `LPerm` (4-constructor list permutation-equivalence) + `refl`/`symm`;
  `sumZ` (Int list sum); ★ `sumZ_lperm` — **sum invariant under `LPerm`** (via Int213's
  propext-free `add_left_comm`).  This is the "reindex the Leibniz sum by a row swap, value
  unchanged" engine.
- **§2 (cornerstone)** `ltCount`/`inversions`/`psign` (`psign l = altSign (inversions l)`);
  ★ `psign_swap_adj` — **an adjacent swap of two distinct values flips the sign**
  (`psign (y::x::l) = −psign (x::y::l)`, `x≠y`).  The concrete `sign(σ∘τ)=−sign σ` for adjacent
  `τ`.  `ac_form` (shared Nat inversion-rearrangement) + `altSign_succ` propext-free.

### Remaining assembly (the next big unit, route A)

1. **§3 enumeration** `permsOf : List Nat → List (List Nat)` (insertion-based: `insertEverywhere`
   + `flatMap`), `perms n = permsOf (range n)`.
2. **§4 the Leibniz determinant** `leibDet n M = sumZ ((perms n).map (fun p => psign p * prodDiag M p))`
   with `prodDiag M p = Πᵢ M i (p.get i)`.
3. **§5 alternating** (the real theorem): swapping rows `a,b` of `M` reindexes the Leibniz sum by
   `σ ↦ σ∘τ` (`τ=(a b)`); this is an `LPerm` of the term list with every term sign-flipped
   (`psign_swap_adj` lifted from adjacent to general `τ` via adjacent-transposition decomposition),
   so `leibDet (rowSwap M) = − leibDet M` (`sumZ_lperm` + global negation), whence equal rows ⟹ 0.
   *Cost*: permutation composition + inverse + the product-reindex `Πᵢ M[τi,σi] = Πⱼ M[j,(σ∘τ)j]`
   + "perms closed under `∘τ` up to `LPerm`".  Heavier than the cofactor involution in line count
   but better-factored (reusable symmetric-group infra), and alternating falls out structurally.
4. **§6 bridge** `leibDet = DetN.det` (Laplace expansion theorem) to transport alternating onto the
   cofactor determinant used by the char-poly/adjugate/Cayley–Hamilton program — OR re-derive the
   cofactor expansion from `leibDet` and use `leibDet` throughout.

Cornerstones §1–§2 are route-A-essential and reusable regardless; §3–§6 is the focused next pass.
