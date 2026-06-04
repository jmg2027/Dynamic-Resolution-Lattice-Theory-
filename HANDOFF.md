# Session Handoff — 2026-06-04 (integer Cayley–Hamilton: matrix ring + char poly banked)

## Branch
`claude/goal-g183-CxU4X` (merged to `main` earlier; develop here).  Full `cd lean && lake build`
clean; every new theorem ∅-axiom (`tools/scan_axioms.py` → `N pure / 0 dirty`, from repo root).

## Headline this session: the matrix ring + the characteristic polynomial

Continuing **Laplace → CH → cfiniteZ_mul** (`research-notes/G185_hadamard_linalg_program.md`),
with the adjugate identity `M·adj M = det M·I` (`Laplace`, 53 PURE) already in hand, built the
infrastructure the integer Cayley–Hamilton telescoping needs.  No `funext`/`propext`/`Quot.sound`/
`Classical`/Mathlib.

- **`Linalg213/CayleyHamilton` (25 PURE)** — the **matrix ring** over `Nat → Nat → Int`:
  - §1 Fubini `sumZ_swap`; §2 ★★ `matMul_assoc`.
  - §3 `matId`/`matAdd`/`matNeg`/`matScalar` + Kronecker-delta sums + `matMul_id_left/right`.
  - §4 distributivity (`matMul_addL/addR`, `matMul_scalarL/negL`) + `matPow`.
  - §5 matrix sums `matSumZ` + `matMul_matSumZ_left/right` (matMul distributes over a matrix sum).
- **`Lib/Math/PolyZ` (16 PURE)** — **integer-coefficient polynomials** (`List Int`, Horner `eval`,
  `addP`/`negP`/`scaleP`/`shiftP`/`mulP`/`coeff`) with full **eval soundness** (`eval_mulP` etc.);
  the `ℕ`-valued `Polynomial213` cannot carry the signed `XI−M`.
- **`Linalg213/PolyDet` (11 PURE)** — the **polynomial determinant** `pdet` + ★★ `eval_pdet`
  (`eval (pdet n A) x = det n (evalMat A x)` — poly-det evaluated = Int det of the evaluated
  matrix), and the **characteristic polynomial** `charPoly M N = pdet N (X·I − M)` with ★
  `eval_charPoly` (`= det N (x·I − M)` for every `x`).  The char poly is now an actual integer
  polynomial; identities about it are proven by evaluation, **reusing the `Int` determinant theory**
  instead of re-deriving cofactor/adjugate over `PolyZ`.

## Open path — the remaining gate (precise plan in `research-notes/G185`, last § Update blocks)

★ **The polynomial uniqueness gate is now CLOSED** (`PolyZ`, 26 PURE): `synth` + factor theorem
`eval_synth`, `roots_bound`, `coeff_zero_of_eval_zero`, ★★ `coeff_unique` (two polynomials agreeing
at every integer have equal coefficients).  This transports the `Int` adjugate identity
(`Laplace.matMul_adj_diag/offdiag`, holds ∀`x` at `A = xI−M`) into a `PolyZ` coefficient identity.

★★★ **Step 4 done** (`Linalg213/CharPolyAdj`, 11 PURE): the **polynomial adjugate identity**
`(X·I − M)·adj(X·I − M) = χ_M·I` over `ℤ[X]` (`padj_identity`) — lifted from the `Int` adjugate
identity by `pmatMul`/`padj` eval-soundness + `coeff_unique`.  The conceptual heart of integer
Cayley–Hamilton is now closed.

★★ **Step 5 (relation extraction) done** (`CharPolyAdj` §4): `cayley_rel_zero` (`−(M·B₀) = c₀·I`)
and `cayley_rel_succ` (`Bₘ − M·B_{m+1} = c_{m+1}·I`), where `Bₖ(i,j) := coeff (padj n charMat i j) k`,
`cₖ := coeff (charPoly M (n+1)) k`.  These are the telescoping inputs.

**Remaining (the home stretch):**
- **Telescoping** ⟹ `χ_M(M) = Σ_{m=0}^{n+1} cₘ Mᵐ = 0`: substitute `c₀ I = −M B₀`, `c_{m+1} I =
  Bₘ − M B_{m+1}` (and `B_{n+1}=0` ⟹ `c_{n+1} I = Bₙ`); the sum telescopes via the index shift
  `Σ_{m≥1} Mᵐ B_{m−1} = Σ_{p≥0} M^{p+1} Bₚ`.  Pure `CayleyHamilton` matrix-sum algebra (`matSumZ`,
  `matPow`, `matMul_addL`, `matMul_matSumZ_*`); recast the relations as matrix equations
  (`matMul M (B 0) = −(c 0 • I)` via `sumZ_map_neg`) + a `matSumZ` reindex lemma.  ⟹ integer CH.
- **§7 Kronecker `M`** (tensor of the two companion matrices) + `V(n+1)=M·V(n)` + first-component
  extraction ⟹ `cfiniteZ_mul` via `cfiniteZ_of_shiftRec`.

This session banked (all ∅-axiom): `CayleyHamilton` 25 + `PolyZ` 33 + `PolyDet` 11 + `CharPolyAdj`
15 = **84 PURE**.  Integer Cayley–Hamilton is now reduced to a finite matrix-sum telescoping.

## Other live threads
- C-finite orbit dimension: `theory/math/analysis/cfinite_orbit_dimension.md`
  (`Cauchy/OrbitDimension`, `Cauchy/CFiniteRing`); `cfiniteZ_add`/`_sub` done, `cfiniteZ_mul` is
  the open ring operation this program closes.
- Number-tower founding (`Lens/Number/`, `book/`) on `main`.

## DRLT Validation Standard
Still the repo's stated real target (untouched): ppb-ppm precision theorem and/or a strict
∅-axiom falsifier (`N_gen=3`, `θ_QCD`).
