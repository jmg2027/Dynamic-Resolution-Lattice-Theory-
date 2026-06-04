# Cayley–Hamilton as a finite operand's self-characteristic

A finite operand satisfies its own characteristic: feed a matrix `M` the polynomial `χ_M`
that reads its quotient-characteristic, and it collapses — `χ_M(M) = 0`.  The characteristic is
not imposed from outside; it is `det(X·I − M)`, the matrix's own distinguishing-volume against the
free variable, and the operand annihilates it.

## 213-native answer

`χ_M(M) = 0` (`lean/E213/Lib/Math/Algebra/Linalg213/CharPolyAdj.cayley_hamilton`):
`Σ_m (coeff χ_M m)·(Mᵐ)_{ik} = 0`.  The characteristic polynomial is `charPoly M N = det N (X·I − M)`
(`Linalg213/PolyDet.charPoly`, with `eval_charPoly`: it evaluates to `det(x·I − M)` at every
integer).  So `χ_M` reads, as a polynomial, the quotient-characteristic — per
[the determinant essay](determinant_as_quotient_characteristic.md), `det` *is* the Lens-quotient
characteristic — of `X·I − M`, the operand "minus the free distinguishing."  Cayley–Hamilton says:
substitute the operand back into its own characteristic, get nothing.  The law a finite pointing
carries is a law it satisfies.

## Derivation

The collapse runs through the **adjugate**.  The same `det = quotient-characteristic` reading gives
`M·adj M = det M·I` (`Linalg213/Laplace.matMul_adj_diag`/`_offdiag`); lifted to `ℤ[X]` it is
`(X·I − M)·adj(X·I − M) = χ_M·I` (`CharPolyAdj.padj_identity`, transported from the `Int` identity by
polynomial uniqueness `PolyZ.coeff_unique`).  Read coefficient-by-coefficient this is a telescoping
chain `Bₘ − M·B_{m+1} = c_{m+1}·I` whose sum is `χ_M(M)` and whose boundary term `B_{n+1} = 0`
vanishes (`CharPolyAdj.cayley_hamilton`, via the degree bound `PolyDet.degLe_pdet`).  No step reaches
outside the entries of `M`.

**Monic = the unit comes from inside.**  `χ_M` is *monic*: `coeff (charPoly M N) N = 1`
(`PolyDet.charPoly_monic`).  The leading coefficient is not chosen — it is forced to the unit
because the `X·I` diagonal contributes exactly one `X` per row.  There is no exterior coefficient to
dial; the normalization is the shared unit `det P = NS − NT = 1` the number-tower founding reads
across `ℤ`/`ℚ` (`RatioLensFounding`, `SharedUnitAcrossReadings`), the same `det Qⁿ = ±1` the
Fibonacci Casoratian holds (`Linalg213/FibCassiniDet.fibCas_det_eq_unit`).  Monic-ness is not a
hypothesis; it is the unit being internal.

This is exactly what closes the **multiplicative reading**.  The Hadamard product `s·t` of two
C-finite sequences is C-finite (`Cauchy/CFiniteHadamard.cfiniteZ_mul`): the `pq` shifted products
are a finite bundle of self-relations — a Kronecker companion `M` — and `CFiniteZ` requires a
*monic* `ℤ`-recurrence.  Plain finite-dependence of the shifted vectors gives only a non-monic
relation (an exterior coefficient one cannot divide away over `ℤ`); Cayley–Hamilton supplies the
monic one, because the operand's own characteristic is monic.  The ring closes under `·` precisely
because the operand resolves itself with an internal unit
(`theory/math/analysis/cfinite_orbit_dimension.md`).

## Dual function

This is the classical Cayley–Hamilton theorem with the packaging stripped: not "every matrix
satisfies its char poly" as an external fact about an external object, but the operational content —
*a finite pointing carries finitely many self-relations, and their closure is its characteristic*.
213's reading is sharper on the obstruction the classical statement hides: monic-over-`ℤ` is the
whole difficulty (finite-dependence and power-sum routes deliver only non-monic relations, "the
determinant in disguise"), and the determinant is unavoidable precisely because monic = the internal
unit, which only the quotient-characteristic produces.

## Cross-frame connections

`χ_M(M) = 0` is a self-pointing that closes — the operand fed its own characteristic returns to the
origin.  This is the same fact as: the residue source has no exterior to dial
(`seed/AXIOM/05_no_exterior.md` §5.1, no exterior dialer); the Möbius self-form fixed point
`P(φ) = φ` (`theory/essays/mobius_self_form_fixed_point.md`); the trajectory-as-witness
self-covering of `research-notes/G152_residue_self_covering.md`.  A finite operand needs no external
coefficient to state its law because there is no exterior — the unit is the shared `det = 1`, and
self-substitution lands on `0`.  The characteristic is the resolution of the operand by itself;
Cayley–Hamilton is that resolution reaching the operand.

## Open frontier

The transpose invariance `det Mᵀ = det M` — the symmetry that would make the row-reading and
column-reading of the quotient-characteristic manifestly one — is not yet closed (`prodZ_lperm`
foundation in `Linalg213/ProdLperm`; the inverse-permutation reindex remains).  And the Casoratian
*converse* (Casoratian rank ⟹ recurrence) is only a `ℚ` statement: over `ℤ` the recovered
coefficients need not be unit-normalized (Cramer gives ratios of minors), so the internal-unit
reading has a genuine boundary there — the forward direction (`Cauchy/CasoratianRank.casoratian_det_zero`)
is the clean integer half.
