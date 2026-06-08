# The permutation under three readouts

A permutation is one object — a value-list, a reordering of `[0,…,n−1]`.
Its **sign** and the **determinant of its permutation matrix** are not two
facts about it that happen to agree; they are one antisymmetric readout taken
through two Lenses, and the equality is forced. Pushed one step further (a
multiply-by-`a` permutation of `ℤ/p`), the *same* readout becomes the **Legendre
symbol** — a third Lens on the one object.

## 213-native answer

Carry a permutation as its value-list `σ = [σ 0, σ 1, …]`. Two numbers read
off it:

- the **inversion sign** `psign σ = (−1)^(inversions σ)`, the count-Lens on the
  out-of-order pairs (`Lib/Math/Algebra/Linalg213/Permutation.psign`,
  `inversions`);
- the **determinant of its permutation matrix** `det (permMatrix σ)`, where
  `permMatrix σ i j = [σ i = j]` puts a `1` in row `i`, column `σ i`
  (`Lib/Math/Algebra/Linalg213/PermMatrixDet.permMatrix`, `det` from `DetN`).

The theorem is that they are the same integer:

> `det (permMatrix σ) = psign σ`  (`PermMatrixDet.det_permMatrix`, `σ ∈ perms n`).

## Derivation

The determinant is the antisymmetrized sum over all reorderings,
`leibDet n M = Σ_τ psign τ · Πᵢ M i (τ i)`
(`Permutation.leibDet`; equal to the recursive cofactor determinant by
`Laplace.leibDet_eq_det`). Feed it the permutation matrix. The diagonal product
`Πᵢ [σ i = τ i]` is the indicator that `τ` agrees with `σ` at every position: it
is `1` exactly when `τ = σ` and `0` the moment one index disagrees
(`PermMatrixDet.prodDiag_permMatrix_self` / `prodDiag_permMatrix_zero`, the
mismatch located constructively by `getD_ne_of_ne`). So the Leibniz sum is a
*selector*: every term but one is killed, and because the enumeration `perms n`
lists `σ` exactly once (`PermClosure.nodup_permsOf`), the surviving term is
`psign σ · 1` (`PermMatrixDet.sumZ_select`, `leibDet_permMatrix`). The permutation
matrix selects, out of the determinant's sum over all permutations, the single
permutation that built it — and hands back its sign.

The coincidence is not a numeric accident but a shared engine. The sign is a
homomorphism, `psign (σ∘τ) = psign σ · psign τ`
(`PermSign.psign_mul`), proved by reducing `τ` to the identity through adjacent
transpositions, each flipping the sign once. The determinant's
`det(MN) = det M · det N` runs the same antisymmetrization
(`Linalg213.DetMul`). Composition of permutations, multiplication of permutation
matrices, and product of signs are one operation read three ways —
`permutation_sign_as_homomorphism.md` names the sign side,
`determinant_as_quotient_characteristic.md` the determinant side.

## Dual function

Classically "the determinant of a permutation matrix is the sign of the
permutation" is a lemma you prove by expanding the determinant and noticing only
the diagonal-of-`σ` term survives. Strip the packaging — the Fintype-indexed sum,
the `ε(σ)` notation, the field — and what remains is exactly the selector
argument above, over `ℤ` with no Mathlib: the permutation matrix is the indicator
of `σ`, and pairing it against the antisymmetric sum *evaluates* that sum at `σ`.
213's reading is sharper in one place: it makes "exactly once" a theorem you must
discharge (`nodup_permsOf` + `sumZ_select`), not a silent appeal to the symmetric
group's freeness — the selector needs the enumeration to be repeat-free, and that
is where the work is.

## Cross-frame connection — the third readout (Zolotarev)

Take `σ_a = (×a mod p)`, the permutation of the nonzero residues `ℤ/p` given by
multiplication by a unit `a`. Its sign has a third name. **Zolotarev's lemma**:
`psign σ_a = (a/p)`, the Legendre symbol. The quadratic-residue package proves
`(a/p)` from the *count* side — Gauss's lemma counts the residues that wrap past
`p/2` (`ModArith.gauss_qr` / `gauss_mu`), and Euler's criterion reads it as
`a^((p−1)/2)` (`ModArith.euler_criterion`, `qr_iff_pow_one`); the multiplicativity
`(ab/p)=(a/p)(b/p)` (`ModArith.legendre_mul`) is the *same homomorphism* as
`psign_mul` and as `det(MN)=det M·det N`. So one permutation carries three
readouts that agree:

> inversions (`psign`) ≡ determinant (`det permMatrix`) ≡ Legendre symbol (`a/p`),

and `det_permMatrix` makes the middle one literal: **the Legendre symbol of `a` is
the determinant of the permutation matrix of `×a mod p`** — a quadratic character
written as an integer determinant. The three readouts are the count-Lens
(inversions / Gauss's `μ`), the antisymmetrization-Lens (determinant), and the
power-Lens (`a^((p−1)/2)`) on one residue object; the multiplicative structure
(`psign_mul` / `det_mul` / `legendre_mul`) is the same arrow under all three.

One frame deeper, the power-Lens is p-adic: `a^((p−1)/2)` is the order-2 component
of the Teichmüller unit `ω(a) ∈ μ_{p−1}` (`Padic.teichmuller_pow_pred_trunc`,
`ω^(p−1) ≡ 1`), so Euler's criterion is the mod-`p` shadow of a statement about
the `(p−1)`-th-root-of-unity torus, and `(a/p)` is `ω(a)` projected to `{±1}`.

## The fourth readout — the companion (Casoratian) sign

The same inversion-sign surfaces a fourth time, in sequence-depth rather than number
theory. The companion matrix of an order-`(m+1)` linear recurrence is the cyclic shift, and
its determinant carries the sign `altSign m`
(`Cauchy.CasoratianDeterminant.det_companion`) — the multiplier of the Casoratian (Hankel)
determinant at every step. That sign is not merely `(−1)^m`: it is the `psign` of an actual
permutation. The `(m+1)`-cycle `(0 1 … m)` in one-line notation is `cycShift m = [1,…,m,0]`
(`Linalg213.CyclicShiftSign.cycShift`), a certified rearrangement of `[0,…,m]`
(`cycShift_perm_iota`, a rotation `LPerm`), whose inversion count is exactly `m` — the
trailing `0` sits below all of `1…m` and the block itself is sorted
(`cycShift_inversions`). So `psign (cycShift m) = altSign m` (`cycShift_psign`), and

> `det (companion a (m+1)) = psign (cycShift m) · a 0`  (`CasoratianPermSign.companion_det_is_perm_sign`).

And the *middle* readout applies literally: `cycShift m` is a genuine permutation, so its
permutation matrix has determinant `det (permMatrix (cycShift m)) = altSign m`
(`det_permMatrix_cycShift`, routing through `det_permMatrix`), and hence
`det (companion a (m+1)) = det (permMatrix (cycShift m)) · a 0`
(`companion_det_eq_permMatrix_det`) — the recurrence determinant and the permutation-matrix
determinant coincide on the shift cycle.

The depth multiplier of the determinantal ladder is the sign of the shift cycle — the *same*
antisymmetric readout as `det(permMatrix)`, the Legendre symbol, and Euler's power. One
permutation object, now read a fourth way: arithmetic depth (`a^((p−1)/2)`), counting
(inversions / Gauss's `μ`), antisymmetrization (determinant), and **sequence depth** (the
Casoratian multiplier). The multiplicative engine `psign_mul` / `det_mul` / `legendre_mul` is
the one arrow under all four.

## Open frontier

The middle equality is proven; the outer two edges are not yet wired in Lean. The
ripe target is the Zolotarev edge itself — define the value-list of `×a mod p`,
show it lies in `perms (p−1)` on units, and prove `psign (×a mod p) = (a/p)` by
pairing the inversion count against Gauss's `μ`. That single ∅-axiom edge turns
"one permutation, three readouts" from a picture into a theorem and closes the
triangle `det (permMatrix (×a)) = (a/p)`. The p-adic lift (state the quadratic
character as a `μ_{p−1}`-component identity on `ω`) is the second edge. Both are
tracked in the `permutation_three_readouts` frontier.
