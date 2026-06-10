# The counting bound behind two representation theorems

A prime is a value of a quadratic form (`a² − ab + b²`, or `a² + b²`) exactly when a single
finiteness fact — a polynomial over `ℤ/p` has no more roots than its degree — forbids every
nonzero residue from being fixed by a power map. The congruence condition (`p ≡ 1 mod 3`,
`p ≡ 1 mod 4`) is not the cause; it is what makes the relevant exponent an integer.

## 213-native answer

The object doing the work is `RootBound.eval_zero`
(`lean/E213/Lib/Math/NumberTheory/PolyRoot/RootBound.lean`): a coefficient-list polynomial `f`
with more pairwise-distinct-mod-`p` roots than `f.length` vanishes mod `p` everywhere — in
particular at `0`, where `eval f 0` is the constant coefficient. Applied to `Tᵐ − 1` (constant
coefficient `−1`, which is `≢ 0 mod p`), it says the `p−1` nonzero residues cannot all be roots.
So some residue `a` has `aᵐ ≢ 1`. That is `NonFixedExists.exists_nonfixed_gen`, and it is
produced **constructively**, by the bounded search `firstNonFixed` whose `none`-branch is the
only thing `eval_zero` refutes. No element is conjured; one is found.

## Derivation

The exponent is the field's only fingerprint on the residue side. For disc-`−3` set `3m = p−1`:
a non-`m`-fixed `a` gives `aᵐ` of multiplicative order 3, i.e. `p ∣ x²+x+1`
(`ModArith.CubeFromFLT.cube_from_nonfixed`,
`Integer.EisensteinConverse.cube_root_exists`). For disc-`−4` set `4k = p−1`, `m = 2k`: a
non-`m`-fixed `a` gives `a^(2k)` a square root of 1 that is not 1, hence `−1`, i.e. `p ∣ x²+1`
(`ModArith.QRNegOne.qr_neg_one`). One lemma `exists_nonfixed_gen`, two exponents — the
generalisation from `3*m = p-1` to `1 ≤ m ∧ m+1 ≤ p-1` is the entire content of making the
disc-`−3` derivation field-agnostic.

The second half is descent: `ℤ[ω]` and `ℤ[i]` are norm-Euclidean
(`Integer.EisensteinDivStep.zomega_div_step`, `Integer.GaussianDivStep.zi_div_step`), so a prime
dividing the cyclotomic norm reduces, with a norm-`p` factor (`split_form` in both
`Integer.EisensteinSplit` and `Integer.GaussianSplit`). Here too the only field-specific number
is the covering radius² — `3/4` for the hexagonal `ℤ[ω]` lattice, `1/2` for the square `ℤ[i]`
lattice (`GaussianDivStep.gaussian_cover`: `4·‖ρ‖²N ≤ 2N²`, against the Eisenstein
`8·‖ρ‖²N ≤ 6N²`). Both radii are `< 1`; that inequality is the norm-Euclidean property
(`div_step_ineq` in each).

## Dual function

This is the splitting law for class-number-one imaginary quadratic fields, read with the
reciprocity packaging stripped: where the textbook invokes quadratic reciprocity or a character
sum to assert `−d` is a residue, the residue is instead exhibited by counting — Lagrange's bound
is a statement about how many roots a coefficient list can have, nothing more. The 213 reading
is sharper precisely because it refuses the existential shortcut: `exists_nonfixed_gen` returns a
witness, not a non-emptiness proof, so each top theorem
(`EisensteinConverse.eisenstein_iff`, `GaussianTwoSquare.two_square_iff`) carries
`#print axioms → "does not depend on any axioms"`.

## Cross-frame connections

Lagrange's bound (a counting fact), the norm-Euclidean covering radius (a geometry-of-numbers
fact), and Fermat's little theorem (`ModArith.UniversalFLT.universal_flt_main`, an order fact)
are the three inputs; the field enters each only as a single scalar — the exponent `(p−1)/3` vs
`(p−1)/4`, the radius² `3/4` vs `1/2`. This is the operational shape of **algebraic priority**
(`CLAUDE.md`: DRLT results come from counting, not continuous variation) and of
**primacy = breadth** (`seed/AXIOM/07_primacy.md` §7.1: the residue reproducing domain after
domain). The disc-`−4` derivation reuses, rather than rebuilds, the disc-`−3` engine: two
theorems, one counting bound, the difference a scalar.

## Open frontier

The boundary is explicit and parametric: for the rational ring `ℤ[√−D]` (`ZSqrt D`, norm
`re² + D·im²`) the covering radius² is `(1+D)/4`, so the norm-Euclidean descent of this form
reaches exactly `D ≤ 2`. The single parametric proof `ZSqrtNegDivStep.zsqrt_div_step`
(`1 ≤ D ≤ 2`) and `ZSqrtNegSplit.split_form` carry `D` as a free `ring_intZ` variable; `D = 1`
recovers the Gaussian split and `D = 2` gives `split_form_two`, the disc-`−8` descent
`p ∣ x²+2 ⟹ p = a² + 2b²`. `D = 3` falls outside (radius² `1` not `< 1`); disc-`−3` closes only
because the half-integer ring `ℤ[ω]` has the smaller radius² `1/3`. The remaining
norm-Euclidean imaginary quadratic fields (`d = 7, 11`, half-integer rings) and the
non-Euclidean class-number-one fields (`d = 19, 43, 67, 163`, PID but not Euclidean — the descent
form does not apply) are untouched. The Pillar-I residue input is also only as general as the
order argument: `−1` (`p ≡ 1 mod 4`) and `−3` (`p ≡ 1 mod 3`) follow from a single
multiplicative-order witness, but `−2` (`p ≡ 1, 3 mod 8`) needs the quadratic character of `2`,
which the bare non-residue search does not supply.  That character is now closed — not from the
non-residue search but from the **Legendre homomorphism**: `(−2/p) = (−1/p)·(2/p)`
(`LegendreMultiplicative.legendre_mul` at `a = p−1`, `b = 2`, with `((p−1)·2) % p = p − 2`),
the two factors being the already-closed first and second supplements
(`EulerFirstSupplement.neg_one_qr_iff`, `SecondSupplement.second_supplement`).  The two
characters agree exactly on `p ≡ 1, 3 (mod 8)`, supplying Pillar I, so the `D = 2` arc now has
the **unconditional congruence iff** `ZSqrtNegTwoSquare.disc_neg_eight_iff`
(`p = a² + 2b² ⟺ p ≡ 1, 3 mod 8`) — the disc-`−8` twin of `two_square_iff`, the necessity half
a square-and-`2·square`-mod-8 enumeration (`form8_residue`).  The remaining
norm-Euclidean imaginary quadratic fields (`d = 7, 11`) and the non-Euclidean class-number-one
fields stay untouched.  The transcendental companion (the period value, `L(1, χ₋₃)` / `Γ(1/3)`)
is separately out of reach.
