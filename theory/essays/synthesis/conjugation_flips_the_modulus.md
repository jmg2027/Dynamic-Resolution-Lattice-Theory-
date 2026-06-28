# Conjugation flips the modulus — a prime's two readouts and why reciprocity is finite

A rational prime `p ≡ 1 (mod 3)` is not one object but a **pair of conjugate readouts** — reduction
mod `π` and mod `π̄` — and conjugation is the map *between* the readouts, never an automorphism
*within* either.  Cubic reciprocity is the statement that the two readouts agree under swapping the
two primes, and that agreement is a finite `μ₃`-group identity.

## 213-native answer

In `ℤ[ω]` (`ω = e^{2πi/3}`) the conjugation `conj⟨a,b⟩ = ⟨a−b, −b⟩` carries a congruence to the
**conjugate modulus**:

> `A ≡ B (mod d)  ⟹  conj A ≡ conj B (mod conj d)`   (`EisensteinConjModEq.conj_modEq`).

It does not fix `d`.  So for a split prime `p = π·π̄` (`EisensteinJacobiPrime.jacobi_splits_p`), the
two reductions `ℤ[ω]/(π)` and `ℤ[ω]/(π̄)` are *conjugate* readouts of `p`, and `conj` is precisely
the arrow swapping them — it maps `ℤ[ω]/(π) → ℤ[ω]/(π̄)`, not `ℤ[ω]/(π)` to itself.

## Derivation

The residue field `ℤ[ω]/(π) ≅ 𝔽_p` is the **prime** field (`EisensteinPrime.norm_prime_euclid`
makes it a field; its size is `p`, prime).  A prime field has *no* nontrivial automorphism.  So an
involution of the ambient ring `ℤ[ω]` cannot descend to an automorphism of `𝔽_p` — `conj` must
**leave** the field, and `conj_modEq` says exactly where it goes: to `ℤ[ω]/(π̄)`.  This is the
load-bearing correction behind the split case of `theory/math/numbertheory/cubic_reciprocity.md`: the
classical exposition's "conjugate law" `χ_π(ᾱ) = conj χ_π(α)` reads as an *intra-field* automorphism
and is false (it would force the rational character of the norm to be trivial); the honest law is the
*inter-modulus* flip.

Whether the involution descends *is* the inert/split dichotomy.  For an inert prime `q ≡ 2 (mod 3)`
(`EisensteinInertPrime`), `q = conj q` is `conj`-stable, the quotient `ℤ[ω]/(q) ≅ 𝔽_{q²}` is the
quadratic field, and there `conj` *does* descend — it is exactly the `q`-power Frobenius
(`EisensteinFrobeniusConj`).  This is the same split / inert / ramified fork the disc−3 lattice runs
in `theory/math/numbertheory/eisenstein_period_arithmetic.md`, now read as "is the modulus
`conj`-stable?"

With conjugation pinned as the swap, reciprocity becomes finite.  Each residue symbol `(π/π')₃`,
`(π'/π)₃` is a cube root of unity (`split_residue_symbol_exists`), and distinct cube roots differ by an
element of norm `3` (`‖ω−1‖² = 3`), so any prime of norm coprime to `3` separates them — a `μ₃`
congruence is forced to an equality (`EisensteinMu3Lift.mu3_eq_of_modEq_pi`).  The two symmetric
Gauss-sum computations (one per modulus, related by the prime-swap) collapse, via the conjugate flip and
the norm-multiplicativity of the character, to two equations in the group `μ₃` — and
`EisensteinCubicReciprocitySplit.mu3_reciprocity_algebra` closes them by a `3⁴`-case `decide`:

> `C = conj E · A²  ∧  E = conj C · S²  ⟹  A = S`,  i.e. `(π/π')₃ = (π'/π)₃`.

The whole law is a finite-group symmetry, the fixed point of the prime-swap involution on the pair of
relations.  Pointing at the syntactic object: there is no analysis anywhere — the closing step is a
truth table over `{1, ω, ω²}⁴`.

## Dual function

This is the classical cubic reciprocity law with its analytic packaging stripped: the Gauss-sum
manipulations that classically look like complex-analytic identities are, read 213-natively, bookkeeping
that delivers a finite `μ₃` cancellation — the law *is* the truth table, and the sums are the route to
it.  The sharpening 213 adds is the modulus flip made syntactic: "the conjugate character" is not a
value-level identity but the arrow `conj_modEq` between two quotients, so the inert/split cases are the
two answers to one decidable question (is `d` an associate of `conj d`?), not two separate theorems.

## Cross-frame connections

The same structure appears in four frames.  *Conjugation as the swap of two readouts* is the count-Lens
reads-out doctrine (`seed/AXIOM/06_lens_readings.md`; `theory/essays/synthesis/two_carriers_one_count.md`):
`Re`/`Im`, `π`/`π̄`, and the two reductions are conjugate readings of one distinguishing, not one
canonical value.  *Reciprocity as a finite-group invariant* is Zolotarev's reading of quadratic
reciprocity as a permutation **sign** (`theory/math/numbertheory/zolotarev.md`) — sign in `S_n` there,
element of `μ₃` here, both forced by a symmetry of a paired construction.  *An involution that need not
descend* is the Cayley–Dickson conjugate at the disc−3 floor (`theory/math/algebra/cayley_dickson/`) and
the abstract sibling of the Hodge `⋆⋆ = id` involution (`theory/math/cohomology/hodge.md`).  And the
collapse-to-finite is the algebraic-priority thesis (DRLT results come from counting, not continuous
variation) made literal: a deep reciprocity law is a decidable fact about a three-element group.

## Open frontier

The supplementary symbols (the units `ω`, `1−ω`), a single statement uniting the inert and split cases,
and a general "an ambient involution descends to `R/(d)` iff `d` is `conj`-stable" lemma — with the `μ_k`
separation and the symmetric-pair closer stated at general `k` to serve quartic reciprocity — remain
unbuilt; the residual directions are tracked in the higher-reciprocity roadmap under `frontiers/`.
