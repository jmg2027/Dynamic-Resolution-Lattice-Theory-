# The permutation sign as the homomorphism the determinant descends from

The sign of a permutation is the **parity of a count** — the inversions of its value-list,
read through the Bool-style involution `±1`. That this parity *multiplies* under composition
(`psign(σ∘τ) = psign σ · psign τ`) is one homomorphism, and both determinant capstones —
`det Mᵀ = det M` and `det(A·B) = det A · det B` — are its corollaries.

## 213-native answer

A permutation is its value-list `[σ 0, σ 1, …, σ (n−1)]`. There is no separate "function
acting on a set" behind the list: the list *is* the data and the action, composed by
`composeList σ τ = τ.map (σ.getD · 0)` realizing `(σ∘τ) i = σ(τ i)`
(`lean/E213/Lib/Math/Algebra/Linalg213/PermGroup.lean`). This is the operation/object
non-separation of `seed/AXIOM/06_lens_readings.md` §6.2 — the pointing and the thing pointed
are one list.

Its sign reads that list twice. First the **count-Lens**: `inversions σ` counts the
out-of-order pairs `i < j` with `σ i > σ j`. Then the **sign-Lens**: `psign σ = altSign(inversions σ)`,
folding the count through the period-2 involution `altSign(k+2) = altSign k`, `±1`
(`lean/E213/Lib/Math/Algebra/Linalg213/Permutation.lean`). The `±1` here is exactly the
Bool-style involution `−(−x) = x` that the sign-Lens applies to a count to give `ℤ` from `ℕ`
(§6.7) — parity is that involution read on the inversion count rather than on a difference.

## Derivation

The homomorphism is not visible in the count: inversions do not add under composition
(`inversions(σ∘τ) ≠ inversions σ + inversions τ` in general). It is recovered by **sorting**.
`PermSign.psign_mul` reduces `τ` to the identity `iota n` one adjacent swap at a time
(`lean/E213/Lib/Math/Algebra/Linalg213/PermSign.lean`): each out-of-order adjacent pair, when
ordered, removes exactly one inversion (`inv_prefix_swap`), and the quantity
`psign(σ∘τ) · psign τ` is **invariant** under that swap — both factors flip (`Q_swap`). When
`τ` reaches `inversions = 0` it equals `iota n` (`sorted_perm_eq_iota`), where the invariant
reads `psign σ · 1`; so the invariant was `psign σ · psign τ` throughout, i.e.
`psign(σ∘τ) = psign σ · psign τ`. The induction is structural on a fuel bound for `inversions τ`
— no well-founded recursion, no `Multiset` quotient, ∅-axiom.

From the homomorphism both capstones fall:

- **`det Mᵀ = det M`.** The inverse permutation has equal sign:
  `psign σ · psign σ⁻¹ = psign(σ∘σ⁻¹) = psign(iota n) = 1` in `{±1}`, so `psign σ⁻¹ = psign σ`
  (`DetTranspose.psign_inv`). The transposed Leibniz term at `σ` is the original term at `σ⁻¹`
  (product-reindex by `σ`), and `perms n` is closed under inversion, so the sum is its own
  reindex (`DetTranspose.det_transpose`).

- **`det(A·B) = det A · det B`.** The diagonal product of `A·B` distributes over the `n^n`
  index functions `funcs n`; the **permutation** ones assemble via
  `leibDet(rowPerm f B) = psign f · leibDet B` — itself a `psign_mul` corollary — into
  `leibDet A · leibDet B` (`DetMul.leibDet_perms_assembly`). The **non**-permutation functions
  repeat a row and vanish, isolated by a constructive `cnt`-pigeonhole (`DetMul.firstDup`,
  `nodup_imp_perm`) that sidesteps the `propext`/`Quot.sound`-carrying `Decidable (a ∈ l)`
  instance (`DetMul.det_matMul`).

## Dual function

This is the classical "sign homomorphism `sgn : Sₙ → {±1}`" with its packaging stripped: there
is no abstract symmetric group acting on an abstract set, only value-lists composed by `getD`,
and `sgn` is not a character to be *defined* on generators and *checked* well-defined — it is
the parity of a count, and its multiplicativity is a sorting invariant. The 213 reading is
sharper exactly at the step classical texts hand-wave ("sign is well-defined because any two
factorizations into transpositions have the same parity"): here that *is* the bubble-sort
descent `Q_swap` + `sorted_perm_eq_iota`, a finite computation, not an appeal to a parity
that pre-exists the factorization.

## Cross-frame connection

The `±1` of `psign` is the same Bool-style involution in three other readings: the sign-Lens
that lifts `ℕ` to `ℤ` (§6.7, `n − m` carries its sign by the swap `−(−x) = x`); the Cassini
period-2 toggle `det 2 (fibCas n) = (−1)ⁿ⁺¹` (`Linalg213/FibCassiniDet`,
`Cauchy/OrbitDimension.cassini_fibZ_step`); and the `altSign` weighting each term of the
cofactor expansion (`Linalg213/DetN`). The determinant's antisymmetry — equal rows ⟹ `det = 0`
— is `psign_mul` read at a fixed point: the row-swap transposition `τ` has `rowPerm τ = id` on
equal rows yet `psign τ = −1`, so the term equals its own negation. Antisymmetry of the wedge,
the count-Lens sign on the quotient (`determinant_as_quotient_characteristic.md`), and the sign
homomorphism are one structural event read three ways.

## Open frontier

The sign theory itself is closed (`psign_mul` ∅-axiom, both capstones built). What it unlocks
remains open: the monic characteristic-polynomial route to the C-finite Hadamard product
(`theory/math/analysis/cfinite_orbit_dimension.md`) now has its alternating-property input —
the live fork named in `determinant_as_quotient_characteristic.md` (whether antisymmetry comes
from Leibniz parity or the cofactor involution) is settled in favor of Leibniz: `psign_mul` is
the parity build, and `det(zI − M)`'s expansion-time antisymmetry is now a corollary, not a
remaining lemma.
