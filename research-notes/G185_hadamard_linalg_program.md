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

### DONE so far (Permutation, 21 PURE; DetN 19 PURE)

- **§1** `LPerm` + `sumZ_lperm` (sum LPerm-invariant).
- **§2** `inversions`/`psign` + `psign_swap_adj` (adjacent head swap of distinct values flips sign).
- **§3** `DetN.altSign_add` (`altSign(a+b)=altSign a·altSign b`); `ltCount_append`,
  `ltCount_cons2_comm`, `psign_cons`, ★ `psign_swap_prefix` — sign flip for a swap of two distinct
  adjacent entries **after any prefix** (the bridge to "swap rows `i,i+1`").
- **§4** `prodDiagFrom`/`leibTerm`/`insertEverywhere`/`permsOf`/`perms`/`leibDet`
  (`leibDet n M = Σ_σ sign(σ)·Πᵢ M i (σ i)`); `leibDet_two_id` sanity (`rfl`); assembly lemmas
  `sumZ_map_neg` (pointwise negation negates the sum) + `map_lperm` (`map` is an `LPerm` congruence).

### Remaining (§5 the real theorem, §6 bridge)

5. **§5 alternating** (the real theorem).  **Per-term identity DONE** (`Permutation` §5, 30 PURE):
   `prodDiagFrom_append`, `rowSwapAt` + `rowSwapAt_{other,at,at1}`, `prodDiagFrom_eq_{below,above}`
   (rows outside `{k,k+1}` unaffected), `prodDiag_rowSwap` (diagonal products agree — two factors
   commute, `mul_left_comm`), and ★ `leibTerm_rowSwap`: an adjacent row swap (rows `k=pre.length`,
   `k+1`) sends the term at `pre ++ y::x::l` to `−(term at pre ++ x::y::l)` for `x≠y`.  The
   determinant's core combinatorial content is proven.
   **The one remaining gate** (to assemble `leibDet (rowSwapAt k M) = − leibDet M` ⟹ equal rows
   ⟹ 0):
   - `LPerm (map (swapAt k) (perms n)) (perms n)` — the enumeration closed under the position-`k`
     swap up to reordering (the genuine combinatorial nut — proving the insertion enumeration
     `permsOf` realizes the symmetric-group action; multi-hundred lines, no `Finset`/Fubini infra).
   - every `p ∈ perms n` has length `n` and **distinct entries** (nodup) — so each `p` decomposes
     `pre ++ y::x::l` at position `k` with `x≠y`, licensing `leibTerm_rowSwap`.
   Same depth as route B's nested-sum involution (essay's prediction); route A's delivered win is
   the clean reusable sign theory + per-term reindex (§1–§5), all banked PURE.
6. **§6 bridge** `leibDet = DetN.det` (Laplace) to transport alternating onto the cofactor
   determinant for char-poly/adjugate/Cayley–Hamilton — or re-derive cofactor expansion from
   `leibDet` and use `leibDet` throughout.

Cornerstones §1–§5 are route-A-essential and reusable regardless; the perms-closure + nodup is the gate.

### Closure development (`Linalg213/PermClosure.lean`) — marathon in progress

The gate `LPerm (map (swapAt k) (perms n)) (perms n)` is being built bottom-up.  **Done (PURE):**
- **§0** clean ∅-axiom `List` membership (`mem_append'`/`map'`/`flatMap'`/`singleton'` — structural
  on `List.Mem`, since core's `mem_*` iff-lemmas are `propext`/`Quot`-tainted).
- **§1** `LPerm.mem` (membership preserved), `lperm_swap_prefix`.
- **§2** soundness: `insEv_sound`, `permsOf_sound` (every enumerated list is a rearrangement).
- **§3** `LPerm.length_eq`; occurrence count `cnt` + `cnt_lperm` (LPerm-invariant).
- **§4** ★ `lperm_of_cnt_eq` — **count-equality ⟹ `LPerm`** (the cancellation engine), via
  `cnt_append`/`cnt_eq_zero_nil`/`cnt_pos_mem`/`mem_split`/`lperm_mid_to_front` +
  `add_left_cancel'` (propext-free replacement for the tainted `Nat.add_left_cancel`).

**DONE (PURE):**
- **§3-§4 generalized** to `{α} [DecidableEq α]` (`cnt` of *lists*; `by_cases` clean on `DecidableEq`).
- **§5** `swapAt_invol` (`swapAt k` twice = id) + `cnt_map_inv` (`cnt q (map f L) = cnt (f q) L` for
  an involution) ⟹ `cnt q (map (swapAt k) (perms n)) = cnt (swapAt k q) (perms n)`.
- **§6** completeness: `mem_map_mpr`/`mem_append_left`/`mem_append_right`/`mem_flatMap_mpr`/
  `insEv_head`/`insEv_complete`/★`permsOf_complete` (`LPerm q xs → q ∈ permsOf xs`).  With
  soundness: **`q ∈ permsOf xs ⟺ LPerm q xs`**.  (22 PURE total.)

**✅ ALTERNATING PROPERTY COMPLETE (PermClosure, 57 PURE).** The full chain is closed:
soundness → completeness → nodup (`nodup_permsOf`, via `removeFirst` retraction) → count engine
(`lperm_of_cnt_eq`) → ★★★ `perms_swap_closed` (enumeration closed under `swapAt`, via `iota` since
`List.range`'s lemmas are dirty) → ★★★ `leibDet_rowSwap` (adjacent row swap negates `leibDet`) →
★★★ `leibDet_eq_zero_of_rows_eq` (**two equal adjacent rows ⟹ `leibDet = 0`**).  The Leibniz
determinant is **alternating**, ∅-axiom, via antisymmetrization — the essay's predicted natural
home, no funext/propext/Quot/Classical.  A full clean ∅-axiom `List` substrate (`mem_*`,
`length_append'`, `map_map'`, `Nodup`-as-`cnt≤1`, …) was built since core's are tainted.

### Determinant property suite COMPLETE (PermClosure, 76 PURE)

alternating (`leibDet_rowSwap`, `leibDet_eq_zero_of_rows_eq`, `leibDet_eq_zero_of_two_rows_eq`,
`leibDet_rows_eq_ne`), multilinearity (`leibDet_setRow_add`/`_smul`), degeneracy
(`leibDet_proportional_rows`, `leibDet_zero_row`).  The defining determinant axioms, ∅-axiom.

### Laplace → CH → cfiniteZ_mul (chosen path; `Linalg213/Laplace.lean` started)

- **§1 relabeling DONE (4 PURE)**: `unshift j` = inverse of `DetN.colShift j`.
- **§2 per-element factorization DONE (Laplace, 19 PURE)** — each perm of `[0,…,n]` is
  `j :: rel.map (colShift j)` (`rel ∈ perms n`):
  - A′ `psign_map_colShift` (sign preserved under the order-embedding `colShift j`, via
    `colShift_lt_mono`/`le_mono` + `inversions_map_colShift`).
  - B′ `prodDiag_minor` (`prodDiagFrom M 1 (rel.map (colShift j)) = prodDiagFrom (minor M j) 0 rel`).
  - C′ `ltCount_perm_colShift` (`ltCount j (rel.map (colShift j)) = j`, via `ltCount_iota` +
    `ltCount_lperm` + `ltCount_colShift_self`).
  - ★ `leibTerm_cons_colShift`: `leibTerm M (j :: rel.map (colShift j)) = altSign j · M 0 j ·
    leibTerm (minor M j) rel`.
  - D-foundation `lperm_of_nodup_mem_iff` (Nodup + same-membership ⟹ `LPerm`).
- **§2 COMPLETE (Laplace, 32 PURE)** ✅ — ★★★ `cofactor_row0`: `leibDet (n+1) M = Σ_{j≤n}
  (−1)ʲ · M 0 j · leibDet n (minor M j)`.  The reindex `perms_succ_lperm` (head-decomposition),
  per-element `leibTerm_cons_colShift`, and the `sumZ`/`flatMap` assembly all done, ∅-axiom.
  **§3 bridge `leibDet_eq_det` ✅** (det properties transferred to `DetN.det`).
- **§4 row-i expansion DONE (Laplace, 46 PURE)** ✅ — `det_rowSwap`, `cyc`/`det_cyc` (moving a row
  to the top multiplies det by `(−1)ⁱ`), `minorAt`/`minor_cyc_eq`, and ★★ `det_cyc_expand`:
  `(−1)ⁱ · det (n+1) M = Σ_{j≤n} (−1)ʲ · M i j · det n (minorAt i j M)` — cofactor expansion along
  ANY row.
  **§5 adjugate DONE (Laplace, 53 PURE)** ✅ — `cofactor_row_i` (signed `(−1)^(k+j)` expansion),
  `matMul`, `adj`, and ★★ `matMul_adj_diag` / `matMul_adj_offdiag`: **`M · adj M = det M · I`**
  (diagonal = row-k expansion; off-diagonal = row-k expansion of the row-replaced matrix +
  `det_rows_eq_ne`).  The heart of Cayley–Hamilton.
  **Next: §6 integer Cayley–Hamilton (`M·adj = det·I`; off-diag = `leibDet_rows_eq_ne` ✅)
  → §5 integer Cayley–Hamilton → §6 Kronecker `M` → `cfiniteZ_mul`.**

- **(done) §2 (D) — the reindex** `LPerm (perms (n+1)) ((iota (n+1)).flatMap (fun j =>
  (perms n).map (fun rel => j :: rel.map (colShift j))))`, via `lperm_of_nodup_mem_iff`:
  - nodup RHS: `nodup_flatMap` (g = the headDecomp, section = `List.head`/recover `j`; each fiber
    nodup via `nodup_map` of the injective `rel ↦ j :: rel.map (colShift j)` over `perms n`).
  - membership equiv `q ∈ perms (n+1) ↔ q ∈ flatMap …`: (⟸) `LPerm (j :: (iota n).map (colShift j))
    (iota (n+1))` (canonical, via cnt) + `map_lperm` + `permsOf_complete`; (⟹) decompose
    `q = j :: tail`, `rel := tail.map (unshift j) ∈ perms n` (multiset `[0,…,n]∖{j} → [0,…,n-1]`),
    `tail = rel.map (colShift j)` (via `colShift_unshift`, `q` nodup ⟹ `j ∉ tail`).
  - **assembly** `cofactor_row0`: `leibDet (n+1) M = sumZ ((iota (n+1)).map (fun j =>
    altSign j · M 0 j · leibDet n (minor M j)))` — `sumZ_lperm` (D) + `cnt`/append over flatMap +
    `map_map'` + `map_eq_of_mem` (`leibTerm_cons_colShift`) + `sumZ_map_smul`.
- **§3 cofactor along any row `i`**: from §2 + multilinearity / row swaps.
- **§4 adjugate** `M · adj M = det M · I`: diagonal = §3; off-diagonal = `leibDet_rows_eq_ne` (✓).
- **§5 integer Cayley–Hamilton** via the adjugate of `zI − M` over `ℤ[z]`.
- **§6 Kronecker `M`** for the Hadamard + extract `cfiniteZ_mul`.

**Next (downstream of alternating):**
- General equal rows (any `a < b`, not just adjacent): move adjacent via `leibDet_rowSwap` swaps.
- `leibDet = DetN.det` (Laplace expansion) — transport alternating to the cofactor determinant.
- Linear dependence (`N+1` vectors in `ℤ^N`) → char poly monic → integer Cayley–Hamilton →
  Kronecker `M` → `cfiniteZ_mul` (the general Hadamard product).

**(Superseded plan below — kept for the proof sketch; all items now done.)**

**Remaining (the home stretch):**
1. **nodup** `Nodup (permsOf xs)` for `Nodup xs`, where `Nodup L := ∀ a, cnt a L ≤ 1` (clean,
   no `Pairwise`).  Plan — the **`removeFirst a`** retraction: for `p ∈ insertEverywhere a r`
   with `a ∉ r`, `removeFirst a p = r` (the inserted `a` is the only one), so `r` is recovered
   from `p`.  Induct on `permsOf ys` (= `P`): `cnt p (flatMap g (r::P')) = cnt p (g r) +
   cnt p (flatMap g P')` (`cnt_append`); if `cnt p (g r) > 0` then `r = removeFirst a p =: r0`
   and `r0 ∉ P'` (nodup `r::P'`), forcing `cnt p (flatMap g P') = 0`; so the sum is `≤ 1`.
   Needs: `removeFirst`, `insEv` nodup (a-position recoverable), `a ∉ r` (from `r ~ ys`,
   `a ∉ ys`), `cnt_flatMap` via `cnt_append`.
2. **count characterization** under nodup: `cnt_eq_of_iff_mem` (`Nodup L → (q∈L ↔ q'∈L) →
   cnt q L = cnt q' L`, via `cnt_pos_of_mem` + `Nat.le_antisymm`).
3. **closure**: `cnt (swapAt k q) (perms n) = cnt q (perms n)` (both `=1`/`0`: `swapAt k q ∈ perms n
   ⟺ LPerm (swapAt k q) range ⟺ LPerm q range ⟺ q ∈ perms n`, sound+complete+`swapAt_lperm`),
   then with §5 ⟹ `cnt q (map (swapAt k)(perms n)) = cnt q (perms n)` ∀q ⟹ `lperm_of_cnt_eq`
   gives the closure `LPerm (map (swapAt k)(perms n)) (perms n)`.
4. **alternating assembly**: `leibDet (rowSwapAt k M) = − leibDet M` (`leibTerm_rowSwap` per-term
   needs each `p ∈ perms n` to decompose `pre++y::x::l` at `k` with `x≠y` — from nodup `p`; then
   `sumZ_map_neg` + `map_lperm` + `sumZ_lperm` + closure), whence equal rows ⟹ `2·leibDet = 0` ⟹
   `0` (ℤ domain).  Then §6-bridge `leibDet = DetN.det` (Laplace) for char-poly/CH.

## Update — §6 the matrix ring + `PolyZ` (CayleyHamilton 25 PURE, PolyZ 16 PURE)

With the adjugate identity `M·adj M = det M·I` banked (Laplace, 53 PURE), the integer
Cayley–Hamilton telescoping needs a **matrix ring** + an **integer-polynomial** layer.  Both
started, ∅-axiom.

**`Linalg213/CayleyHamilton.lean` (25 PURE)** — the matrix ring over `Nat→Nat→Int`:
- **§1 Fubini** `sumZ_map_zero`, ★ `sumZ_swap` (finite double-sum swap), `sumZ_map_smul_right`.
- **§2** ★★ `matMul_assoc` (matrix multiplication associative, via Fubini).
- **§3** `matId`/`matAdd`/`matNeg`/`matZero`/`matScalar`; ★ Kronecker-delta sums
  `sumZ_iota_delta_ge`/`_lt`; ★ `matMul_id_left`/`_right` (`I·M=M`, `M·I=M` at in-range indices).
- **§4** ★ distributivity `matMul_addL`/`_addR`, `matMul_scalarL`, `matMul_negL` (+ `sumZ_map_neg`,
  `neg_zero'`); `matPow` (`M^0=I`, `M^{k+1}=M·M^k`).
- **§5** `matSumZ` (entrywise matrix sum over a `List Nat`); ★ `matMul_matSumZ_right`/`_left`
  (matMul distributes over a matrix sum, via Fubini) + `matSumZ_add`.

**`Lib/Math/PolyZ.lean` (16 PURE)** — integer-coefficient polynomials (the `ℕ`-valued
`Polynomial213` cannot carry the signed `xI−M`):
- `PolyZ := List Int` (low-to-high), Horner `eval`, `C`/`Xp`/`addP`/`negP`/`scaleP`/`shiftP`/
  `mulP`/`coeff`.
- ★ **eval soundness** `eval_C`/`eval_Xp`/`eval_addP`/`eval_scaleP`/`eval_shiftP`/`eval_negP`/
  ★★`eval_mulP` — each op commutes with evaluation (`PolyZ` is a commutative-ring reflection of
  `Int`).

### The concretized remaining plan (eval + uniqueness, reusing the Int adjugate)

The key move that AVOIDS re-deriving the cofactor/adjugate theory over `PolyZ`: get the
characteristic-polynomial coefficients via a **recursive poly-det** but prove the adjugate
identity over `PolyZ` by **evaluation + uniqueness**, transporting the Int identity
`matMul (xI−M) (adj (xI−M)) = det(xI−M)·I` (already ∅-axiom, holds for every integer `x`).

1. **poly-det** `pdet : Nat → (Nat→Nat→PolyZ) → PolyZ` (recursive cofactor, ~10 lines) + poly
   matrix ops; **eval-soundness** `eval (pdet A) x = det (evalMat A x)` and eval over poly-matMul
   (via `eval_addP`/`eval_mulP`).
2. **uniqueness** `(∀ x, eval p x = eval q x) → trim p = trim q` (or coeff-wise).  Route:
   **Vandermonde-via-adjugate** — `V·c = 0` (the eval-at-`0..L-1` vector) with `V` the Vandermonde
   matrix; `adj V · V = det V · I` (the **Int adjugate identity, reused**) ⟹ `det V · c_k = 0`;
   `det V ≠ 0` (distinct integer nodes) + `ℤ` integral-domain ⟹ `c_k = 0`.  (Vandermonde
   `det ≠ 0` = the product-of-differences determinant — a bounded sub-lemma.)  Alternative route:
   remainder theorem `p(X)=(X−r)q(X)+p(r)` + root-count induction (needs synthetic division on the
   low-to-high list).
3. **charMat** `xI−M` as a poly-matrix; `χ := pdet charMat` (monic, integer); `padj := poly-adj`.
   Adjugate identity over `PolyZ` `charMat · padj = χ • polyId` by eval-at-all-`x` (step 1 +
   the Int adjugate) + uniqueness (step 2).
4. **telescoping** read the `PolyZ` identity coefficient-wise: `B_k := coeff-matrix of padj`,
   `c_k := coeff χ`; relations `−M B_0 = c_0 I`, `B_{k-1}−M B_k = c_k I`, `B_{N-1}=I`; then
   `χ(M) = Σ c_k M^k = 0` by the index-shift telescoping — consumes §4/§5 matrix-ring laws
   (`matMul_addL`, `matMul_matSumZ_*`, `matPow`).  ⟹ ★★★ integer Cayley–Hamilton `χ(M)=0`.
5. **§7 Kronecker `M`** from the two companion recurrences; `V(n+1)=M·V(n)`; apply CH; the first
   component yields the monic shift recurrence ⟹ `cfiniteZ_of_shiftRec` ⟹ `cfiniteZ_mul`.

The matrix-ring (§1–§5) + `PolyZ` are banked and route-independent; the gate is now step 2
(polynomial uniqueness) which itself **reuses the Int adjugate identity** (Vandermonde route).

## Update — poly-det + characteristic polynomial banked (PolyDet 11 PURE)

`Linalg213/PolyDet.lean` (11 PURE) — the polynomial determinant and the characteristic
polynomial, **reusing the `Int` determinant via evaluation** (no cofactor/adjugate re-derivation
over `PolyZ`):
- `pdet n A` (row-0 cofactor recursion over `PolyZ`-entried `A`); ★★ `eval_pdet` —
  `eval (pdet n A) x = det n (evalMat A x)` (poly-det evaluated = Int det of evaluated matrix).
- `charMat M = X·I − M`, `charPoly M N = pdet N (charMat M)`; ★ `eval_charPoly` —
  `eval (charPoly M N) x = det N (x·I − M)` for every integer `x`.  **The characteristic
  polynomial now exists as an actual integer-coefficient list with the right values.**

### The remaining gate, precisely: polynomial uniqueness (then telescoping)

Everything downstream needs **`eval`-equal ⟹ coefficient-equal** to transport the `Int` adjugate
identity (`Laplace.matMul_adj_diag/offdiag`, holds for every integer `x` at `A = xI−M`) into the
`PolyZ` identity `charMat · padj = χ • I`, whose coefficient-comparison telescopes to `χ(M)=0`.

**Chosen route — the factor theorem + root bound (constructive, no Vandermonde det):**
1. `synth p r : PolyZ` (synthetic-division quotient, low-to-high) with
   `eval p x = eval p r + (x − r) * eval (synth p r) x` (proven by Horner induction; the recursion
   `synth (a::p') r = (eval p' r) :: synth p' r`).  ⚠ `synth` preserves `length` (trailing `0`):
   use `eval`-ignores-trailing-zero, or bound the *effective* degree, so the root-count induction
   strictly decreases.
2. `roots_bound` : `length p ≤ L → (p vanishes at L distinct integer nodes) → ∀x, eval p x = 0`,
   by induction on `L`: factor at `r₀` (step 1), the quotient vanishes at the remaining `L`−1 nodes
   (ℤ integral domain `Int213.mul_eq_zero`, nodes distinct), recurse.
3. `coeff_unique` : `(∀x, eval p x = eval q x) → ∀k, coeff p k = coeff q k` — apply `roots_bound`
   to `addP p (negP q)` over `length`+1 nodes `0,1,…`.  (`eval_addP`/`eval_negP` already give
   `eval (p − q) x = 0`.)
4. **PolyZ adjugate** `padj := poly-adj charMat` (an `adj` mirrored over `PolyZ`, or via
   `coeff`-of-`pdet`-of-minors); identity `charMat · padj = χ • polyId` by `eval`-at-all-`x`
   (Int adjugate + `eval_pdet`) + `coeff_unique`.
5. **telescoping**: `B_k := coeff-matrix k of padj`, `c_k := coeff χ k`; relations `−M B_0 = c_0 I`,
   `B_{k−1} − M B_k = c_k I`, `B_{N−1} = I`; index-shift ⟹ `χ(M) = Σ_k c_k M^k = 0` — consumes the
   §4/§5 matrix-ring laws (`matMul_addL`, `matMul_matSumZ_*`, `matPow`).  ⟹ ★★★ integer CH.
6. **§7 Kronecker `M`** + first-component extraction ⟹ `cfiniteZ_mul` (`cfiniteZ_of_shiftRec`).

Banked this session (route-independent, all PURE): the matrix ring (`CayleyHamilton` 25),
`PolyZ` (16), `PolyDet`/`charPoly` (11).  **Next concrete unit: step 1–3 (polynomial uniqueness).**

## Update — ★ polynomial uniqueness gate CLOSED (PolyZ 26 PURE)

The gate of the whole CH program — `eval`-equal ⟹ coefficient-equal — is **done, ∅-axiom**
(`PolyZ`, steps 1–3 of the prior plan):
- `synth p r` (synthetic-division quotient, low-to-high, no trailing zero) + ★ **factor theorem**
  `eval_synth`: `p(x) = p(r) + (x−r)·(synth p r)(x)` (Horner induction, `ring_intZ`), and
  `length_synth_cons` (drops exactly one degree).
- ★ `roots_bound`: a polynomial of length `≤ L` with `L` distinct integer roots is the zero
  function (induction on `L`; factor at a root; `Int213.mul_eq_zero` integral domain).
- ★ `coeff_zero_of_eval_zero`: vanishes everywhere ⟹ all coefficients `0` (peel the constant
  term `a₀ = p(0)`, bridge the `x=0` gap via `roots_bound` at nodes `1,2,…`).  ⚠ `Nat.succ_ne_zero`
  is propext-dirty — use `Nat.noConfusion`.
- ★★ `coeff_unique`: two polynomials agreeing at every integer have equal coefficients
  (`roots_bound` on `p − q`, `coeff_addP`/`coeff_negP`).

This is the lemma that lets the `Int` adjugate identity (`Laplace.matMul_adj_diag/offdiag`, holds
∀`x` at `A = xI−M`) be transported into the `PolyZ` matrix identity `charMat·padj = χ•I` by
evaluation, then read coefficient-wise for the telescoping.

**Remaining (steps 4–6, all infrastructure now in place):**
4. `pmatMul` (PolyZ matrix product) + eval-soundness; `padj` (poly-adjugate of `charMat`, mirrors
   `Laplace.adj` over `PolyZ`) + eval-soundness; the entrywise identity `pmatMul charMat padj =
   χ • polyId` by eval-at-all-`x` (Int adjugate + `eval_pdet`/`eval_pmatMul`) + `coeff_unique`.
   (New file importing `Laplace` + `PolyDet` + `CayleyHamilton`.)
5. telescoping `χ(M) = Σ_k c_k M^k = 0` (`B_k := coeff-matrix of padj`, `c_k := coeff χ`; the
   relations from step 4 read at each power; index-shift via §4/§5 matrix-ring laws) ⟹ ★★★ CH.
6. §7 Kronecker `M` + first-component extraction ⟹ `cfiniteZ_mul`.

## Update — ★★★ polynomial adjugate identity CLOSED (CharPolyAdj 11 PURE)

Step 4 done, ∅-axiom (`Linalg213/CharPolyAdj.lean`): **`(X·I − M)·adj(X·I − M) = χ_M·I` over `ℤ[X]`**.
Matrix products/adjugates over `PolyZ` carry evaluation soundness — `pmatMul`+`eval_pmatMul`,
`padj`+`eval_padj` (`eval (padj n A a b) x = Laplace.adj n (evalMat A x) a b`) — so the identity is
**lifted from the `Int` adjugate identity by evaluation + `coeff_unique`**, re-deriving nothing over
`PolyZ`:
- `padj_identity_eval`: at every `x`, entry `(i,k)` of `(XI−M)·adj` evaluates to the `Int` adjugate
  value (`matMul_congr` to swap in `evalMat`, then `Laplace.matMul_adj_diag`/`_offdiag`;
  `eval_charPoly` for the diagonal `χ`).
- ★★★ `padj_identity`: `∀ kk, coeff (pmatMul (n+1) charMat padj i k) kk = coeff (charScalarId M (n+1) i k) kk`
  (i.e. equal as integer polynomials) via `coeff_unique`.

**Remaining (steps 5–6):**
5. **Telescoping** ⟹ `χ(M) = Σ_k c_k M^k = 0`.  Read `padj_identity` coefficient-wise: need
   `coeff_psumZ` (coeff of a `PolyZ` sum) + `coeff_mulP` (coeff of a product = convolution) + the
   length-≤2 `charMat M i j = [−M_ij, δ_ij]`, giving the matrix relations `B_{k−1} − M B_k = c_k I`
   (`B_k(i,j) := coeff (padj … i j) k`, `c_k := coeff χ k`), boundary `B_{N−1}=I`, `−M B_0 = c_0 I`;
   then the index-shift telescoping with §4/§5 `CayleyHamilton` ring laws (`matMul_addL`,
   `matMul_matSumZ_*`, `matPow`).  ⟹ integer Cayley–Hamilton.
6. **§7 Kronecker `M`** (tensor of the two companion matrices) + `V(n+1)=M·V(n)` + first-component
   extraction ⟹ `cfiniteZ_mul` via `cfiniteZ_of_shiftRec`.

Banked this session (all ∅-axiom): matrix ring (`CayleyHamilton` 25) + `PolyZ` 26 (incl. the
uniqueness gate) + `PolyDet`/`charPoly` 11 + `CharPolyAdj` 11 = **73 PURE**.  The conceptual heart
(uniqueness + polynomial adjugate identity) is done; steps 5–6 are coefficient bookkeeping + the
companion-matrix construction.
