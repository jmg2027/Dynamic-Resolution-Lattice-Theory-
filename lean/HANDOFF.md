# Session Handoff — 2026-06-04 (determinant tower → Cayley–Hamilton → Hadamard → Casoratian rank)

## Branch / build
On `main` (work merged + pushed).  Full `cd lean && lake build` clean; every new theorem ∅-axiom
(`tools/scan_axioms.py` → `N pure / 0 dirty`; `#print axioms` → "does not depend on any axioms").

## What this marathon delivered (all ∅-axiom, from scratch — no Mathlib, no `sorry`, no axioms)

A complete `n×n` integer determinant theory and three major applications:

- `Linalg213/{Permutation,PermClosure,Laplace}` — Leibniz determinant, **alternating** (via
  antisymmetrization), multilinear, cofactor expansion, **adjugate identity** `M·adj M = det M·I`.
- `Linalg213/{CayleyHamilton,PolyDet,CharPolyAdj}` + `PolyZ` — ★★★ **integer Cayley–Hamilton**
  `χ_M(M)=0` + the recurrence bridge `ch_recurrence`.
- `Cauchy/CFiniteHadamard` — ★★★ **C-finite Hadamard product** `cfiniteZ_mul`
  (`CFiniteZ s → CFiniteZ t → CFiniteZ (s·t)`) — the last C-finite ring operation.
- `Linalg213/RowDependence` + `Cauchy/CasoratianRank` — ★★ row-dependence ⟹ `det=0`; **C-finite ⟹
  Casoratian rank ≤ order** (`casoratian_det_zero`), with the **Fibonacci witness**
  `fib_casoratian_rank` (rank exactly 2 = orbit dimension).

The C-finite sequences are now a **commutative ring** under `+` and pointwise `·`.  Narrative:
`theory/math/linalg213.md` + `theory/math/analysis/cfinite_orbit_dimension.md`.

## Next directions (rough order)

1. **Casoratian converse** (rank `k` ⟹ order-`k` recurrence).  ⚠ Over `ℤ` subtle: Cramer gives
   *rational* coefficients (monic only if the `k×k` minor is `±1`) — the clean biconditional is a
   `ℚ` statement, not `CFiniteZ`.  The forward direction is the clean integer result (done).
2. **More determinant theorems** (bounded, further pay off the tower):
   - `det Mᵀ = det M` (transpose) — unlocks *column* ops; needs the inverse permutation on the list
     rep + sign invariance (~100 lines).
   - **Vandermonde** `det[xᵢʲ] = Π_{i<j}(xⱼ−xᵢ)` — via "det is a polynomial in the last point with
     known roots" (reuses `PolyZ`) or column ops (needs transpose).
   - `det(AB) = det A · det B` (multiplicativity) — needs the unique-alternating-form characterization.
   - **Triangular** `det = Π Mᵢᵢ` — bounded; row-0 cofactor peels `M₀₀`, induct on the minor (needs
     `iota (n+1) = 0 :: (iota n).map succ` + a `prodZ`).
3. **Holonomic = `ℚ(n)`-orbit** — the top rung (rational-function coefficients; Apéry ζ(3)).  Large.

## DRLT Validation Standard
Still the repo's stated real target (untouched here): a ppb–ppm precision theorem and/or a strict
∅-axiom falsifier (`N_gen=3`, `θ_QCD`).
