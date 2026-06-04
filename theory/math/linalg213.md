# Linear Algebra 213

**Status**: Closed.  Two towers: (1) the original Real213 vector / span / rank / Gram +
phase-chiral bridge; (2) the **integer determinant → Cayley–Hamilton** tower — a from-scratch
∅-axiom `n×n` determinant theory over `ℤ` culminating in `χ_M(M)=0`, which closes the C-finite
**Hadamard product** (see [`analysis/cfinite_orbit_dimension.md`](analysis/cfinite_orbit_dimension.md)).

## Overview

213-native linear algebra: vectors, span, rank, Gram matrix,
phase-chiral bridge (G4 anchor).  Realized on Real213 cuts +
SignedCut for signed extensions.  Plus a self-contained **integer matrix theory** built with
no Mathlib, no `sorry`, no axioms — the determinant tower below.

## Lean source

- **Sub-tree**: `lean/E213/Lib/Math/Linalg213/`
- **Umbrella**: `Linalg213.lean`
- **∅-axiom status**: PURE

## Narrative

Vectors are `Fin n → Real213`, span is finite-set generation,
rank is decidable (Gaussian elimination on rational pivots).

The **PhaseChiralBridge** (`PhaseChiralBridge.lean`) is the
formal anchor for G4 (d = 5 chiral / phase duality): the same
underlying 5-dim Linalg213 carrier admits two distinct readings
(chiral basis vs phase basis), related by a structural change-of-
basis.

Used downstream by:
- α_em Gram-self-energy (`AlphaEM/GramSelfConsistency.lean`)
- Hodge index theorems (Hodge chapter)

## The integer determinant → Cayley–Hamilton tower

A second, independent tower builds the `n×n` determinant over `ℤ` from scratch and proves
**integer Cayley–Hamilton** `χ_M(M) = 0`, then applies it to close the C-finite Hadamard product.
A matrix is a total function `M : Nat → Nat → Int` with an explicit dimension; **all** reasoning
is pointwise (`funext` is `Quot.sound`-dirty, so matrix-as-function equalities go through pointwise
congruence — the ∅-axiom matrix-work pattern).  No Mathlib, no `sorry`, no axioms; a clean `List`
substrate (`mem_*`, `length_append'`, `map_map'`, `Nodup`-as-`cnt≤1`, `iota`) was rebuilt because
core's are `propext`/`Quot`-tainted.

### The determinant (the alternating property via antisymmetrization)

- **`Permutation`** — the **Leibniz determinant** `leibDet n M = Σ_σ sign(σ)·Πᵢ M i (σ i)`, with the
  sign as inversion parity (`psign`).  `LPerm` is a four-constructor list permutation-equivalence;
  `sumZ_lperm` (a sum is `LPerm`-invariant) is the engine that reindexes the Leibniz sum under a row
  swap.
- **`PermClosure`** — the symmetric-group machinery: the enumeration `perms n` is sound, complete
  (`q ∈ permsOf xs ⟺ LPerm q xs`), and `Nodup`, with the **count engine** `lperm_of_cnt_eq`
  (count-equality ⟹ `LPerm`, the cancellation-free master tool).  ⟹ the **alternating** property
  `leibDet_rowSwap` (an adjacent row swap negates) and `leibDet_eq_zero_of_rows_eq` (two equal rows
  ⟹ `0`) — the determinant's defining antisymmetry, the essay's predicted natural home
  ([`essays/determinant_as_quotient_characteristic.md`](../essays/determinant_as_quotient_characteristic.md)).
  Plus multilinearity (`leibDet_setRow_add`/`_smul`) and degeneracy.
- **`Laplace`** — the **cofactor (Laplace) expansion** (`cofactor_row0`, then `cofactor_row_i` along
  any row via the row-cycle `cyc`/`det_cyc`), the bridge `leibDet_eq_det` to the recursive
  `DetN.det`, and the **adjugate identity** `M · adj M = det M · I` (`matMul_adj_diag`/`_offdiag`) —
  the heart of Cayley–Hamilton.

### Integer Cayley–Hamilton

- **`CayleyHamilton`** — the **matrix ring** over `Nat → Nat → Int`: finite-sum Fubini `sumZ_swap`,
  `matMul_assoc`, the identity laws (via Kronecker-delta sums), distributivity, scalar/neg, `matPow`
  (with `matPow_succ_right`: `Mᴺ·M = Mᴺ⁺¹`), and matrix sums `matSumZ`.
- **`PolyZ`** (`Lib/Math/PolyZ.lean`) — **integer-coefficient polynomials** (`List Int`, Horner
  `eval`) with full eval-soundness, the **uniqueness gate** (`synth` factor theorem → `roots_bound`
  → `coeff_unique`: two polynomials agreeing at every integer have equal coefficients — proven
  constructively via a root bound over the `ℤ` integral domain), and a coefficient **degree bound**
  `degLe`.
- **`PolyDet`** — the **polynomial determinant** `pdet` with `eval_pdet` (`eval (pdet n A) x =
  det n (evalMat A x)`), the **characteristic polynomial** `charPoly M N = pdet N (X·I − M)` with
  `eval_charPoly`, the degree bound `degLe_pdet`, and **monicity** `charPoly_monic`
  (`coeff (charPoly M N) N = 1`).
- **`CharPolyAdj`** — the centerpiece.  The `Int` adjugate identity is **lifted to `ℤ[X]`** by
  evaluation + `coeff_unique` (`padj_identity`: `(X·I−M)·adj(X·I−M) = χ_M·I`, no cofactor/adjugate
  theory re-derived over `PolyZ`).  Reading it coefficient-wise gives the relations `M·B₀ = −c₀·I`,
  `M·B_{m+1} = Bₘ − c_{m+1}·I`; the **telescoping** (with the boundary `B_{n+1}=0` from the degree
  bound) yields ★★★ **`cayley_hamilton`**: `Σ_{m=0}^{n+1} (coeff χ_M m)·(Mᵐ)_{ik} = 0`, i.e.
  `χ_M(M) = 0`.  The **recurrence bridge** `ch_recurrence` turns this into: a vector sequence with
  `w(n+1)=M·w(n)` has every component obey the monic order-`(N+1)` `χ_M`-recurrence.

### Downstream: the C-finite Hadamard product

`Cauchy/CFiniteHadamard.cfiniteZ_mul` uses the recurrence bridge on the **Kronecker companion** of
the `pq` shifted products `w(n)_{(a,b)} = s(n+a)·t(n+b)` (the companion factors as `Ms·Mt`), closing
`CFiniteZ s → CFiniteZ t → CFiniteZ (s·t)` — the last C-finite ring operation.  The flat↔grid index
bijection needed there is a fresh ∅-axiom **fuel-structural `divmod`** (core `Nat./`/`%` are
`propext`/`Quot`-dirty).

## Connection

- `research-notes/G4_chiral_phase_duality.md` (active foundational)
  — anchored here
- `theory/physics/alpha_em/precision_derivation.md` — Gram correction
- `research-notes/G185_hadamard_linalg_program.md` — the determinant → Cayley–Hamilton →
  Hadamard program log (the tower above; ready to archive)
- `theory/essays/determinant_as_quotient_characteristic.md` — the alternating-as-antisymmetrization
  intuition that chose the Leibniz route
