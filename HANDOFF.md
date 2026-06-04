# Session Handoff — 2026-06-04 (determinant tower → Cayley–Hamilton → Hadamard → Casoratian + det properties)

## Branch / build
On `main` (merged + pushed).  Full `cd lean && lake build` clean; every new theorem ∅-axiom
(`tools/scan_axioms.py` → `N pure / 0 dirty`; `#print axioms` → "does not depend on any axioms").

## Delivered this marathon (all ∅-axiom, from scratch — no Mathlib, no `sorry`, no axioms)

A complete `n×n` integer determinant theory + applications + a full elementary-property suite:

- **Core tower** `Linalg213/{Permutation,PermClosure,Laplace}` — Leibniz determinant, **alternating**
  (antisymmetrization), multilinear, cofactor expansion, **adjugate** `M·adj M = det M·I`.
- **Cayley–Hamilton** `Linalg213/{CayleyHamilton,PolyDet,CharPolyAdj}` + `PolyZ` — ★★★ `χ_M(M)=0`
  + the recurrence bridge.
- **Hadamard product** `Cauchy/CFiniteHadamard` — ★★★ `cfiniteZ_mul` (the C-finite ring is closed).
- **Casoratian rank** `Cauchy/CasoratianRank` (+ `Linalg213/RowDependence`) — ★★ C-finite ⟹ Casoratian
  rank ≤ orbit dimension, with the **Fibonacci witness** (rank exactly 2).
- **Elementary determinant properties** (this round):
  - `RowDependence`: `det_row_combo_zero` (row = combo of others ⟹ 0), `det_addRowMul` (row op invariance).
  - `DetTriangular`: `det_lower_triangular` (`det = Π Mᵢᵢ`), `det_matId` (`det I = 1`).
  - `DetScale`: `det_smul` (`det (c·M) = cⁿ·det M`).
  - `DetZeroCol`: `det_zero_col` (zero column ⟹ 0, column analog via Leibniz — no transpose).

Narrative: `theory/math/linalg213.md` + `theory/math/analysis/cfinite_orbit_dimension.md`.

## Next directions (rough order)
1. **`det Mᵀ = det M`** (transpose) — the keystone for *column* operations (then Vandermonde,
   Cramer).  ~150 lines: inverse permutation on the list rep + product-reindex
   `Π M(pᵢ,i) = Π M(i,(p⁻¹)ᵢ)` + `psign p = psign p⁻¹` + `perms` closed under inverse (count engine).
   NB: the Casoratian thread does *not* need it (the Hankel matrix is symmetric).
2. **`det(AB) = det A · det B`** — needs the unique-alternating-multilinear-form characterization.
3. **Vandermonde** `det[xᵢʲ] = Π_{i<j}(xⱼ−xᵢ)` — via column ops (needs transpose) or "det as a
   polynomial in the last point with known roots" (reuses `PolyZ`).
4. **Casoratian converse** — ⚠ over `ℤ` only a `ℚ` statement (Cramer gives rational coefficients).
5. **Holonomic = `ℚ(n)`-orbit** — the top rung (rational-function coefficients; Apéry ζ(3)).  Large.

## DRLT Validation Standard
Still the repo's stated real target (untouched by this math thread): a ppb–ppm precision theorem
and/or a strict ∅-axiom falsifier (`N_gen=3`, `θ_QCD`).
