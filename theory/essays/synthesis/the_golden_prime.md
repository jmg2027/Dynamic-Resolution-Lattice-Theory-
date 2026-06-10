# The golden prime — value and valuation as two faces of `ℚ(√5)`

`5` is the prime where the golden recurrence's analytic reading (its limit
`φ`) and its arithmetic reading (the `5`-adic valuation of its Fibonacci
convergents) are the *same* fact, because `5` is the one ramified place of
the single field `ℚ(√5)` both readings live in.

## 213-native answer

The golden recurrence `s_{n+1} = s_n + s_{n-1}` carries two readouts of one
object.  Read analytically, its convergent cut converges to `φ`
(`PhiCut`, `theory/math/numbersystems/real213.md`), and the deployment
reads that limit as the golden modulus `R_u = 1/φ²`
(`theory/physics/cp_phase.md`).  Read arithmetically, the same recurrence's
integer terms `F_n` have a `5`-adic valuation `ν₅(F_n) = ν₅(n)`
(`fibN_val_law`, `theory/math/numbertheory/fibonacci_5adic_valuation.md`).
The prime `5` is where these two readouts coincide: it is the discriminant
of `x² − x − 1`, hence the unique ramified prime of `ℚ(√5) = ℚ(φ)`, the one
field that hosts both `φ` (the value) and `F_n` (whose valuation the branch
measures).

## Derivation

Ramification is the syntactic hinge.  Over `𝔽₅`, `x² − x − 1 ≡ (x − 3)²` —
a double root, `α ≡ β ≡ 3`.  The two Binet branches `αⁿ`, `βⁿ` that
separate `φ`'s value from its conjugate collapse in status at `5`, and the
collapse is exactly what the FSM reads: the Fibonacci FSM mod `5` has
period `20 = 4·5` with its zero-set on the multiples of `5`
(`five_dvd_fib_iff`: rank of apparition `α(5) = 5`), while Lucas — same
recurrence, regular branch `L_n ≡ 2·3ⁿ` — never vanishes
(`lucasMod5_never_zero`).  Singular branch `F_n ≡ n·3ⁿ⁻¹` vanishing on
`5·ℕ`, regular branch never: the value-conjugation that defines `φ` and the
valuation-rank that defines `ν₅(F_n)` are one event at the double root.

That one event lifts to all orders.  The index-multiplication recurrence
`F_{b+2m} = L_m F_{b+m} − (−1)ᵐ F_b` (`fibZ_index_rec`) iterates to the
quintupling identity `F_{5m} = F_m·(25F_m⁴ + 25(−1)ᵐF_m² + 5)`
(`fibZ_quintuple`), whose cofactor `≡ 1 mod 5` supplies exactly one factor
of `5` per quintupling — the lift `ν₅(F_{5m}) = ν₅(F_m) + 1` that closes
`ν₅(F_n) = ν₅(n)`.  The `(−1)ᵐ` driving that identity is the Cassini sign
`F_{m+1}² − F_m F_{m+1} − F_m² = (−1)ᵐ` (`fibZ_cassini_eps`) — the
unimodular `det = ±1` that `OrbitDimension` already identifies with the
number-tower's conserved unit `det P = NS − NT = 1`
(`PnFibonacciUniversal.det_pn_universal`).  So the unit that pins `φ`'s
continued-fraction lowest-terms IS the sign that drives the valuation lift.

## Dual function

Classically these are two unrelated facts about `5`: "the golden ratio is
`(1+√5)/2`" (a value) and "`5` is the rank of apparition of the Fibonacci
sequence" (a divisibility curiosity).  213 reads them as one — the value
`φ` and the valuation `ν₅(F_n)` are the analytic and `p`-adic faces of
`ℚ(√5)` at its ramified prime, and the same Cassini unit `±1` underwrites
both.  The refinement 213 adds is that "`5` is ramified" stops being a
background field fact and becomes syntactic: the FSM period `4·5ᵏ`, the
double root mod `5`, the quintupling cofactor `≡ 1 mod 5`.  You can point
at the ramification.

## Cross-frame connections

The same field `ℚ(√5)` resolves five ways: the **value** `φ` (the cut
limit, `PhiCut`); the **modulus** `R_u = 1/φ²` (`cp_phase`); the
**valuation** `ν₅(F_n) = ν₅(n)` (`fibN_val_law`); the **unit** `det = ±1`
(`cassini_fibZ`, shared with the number-tower); and the **sign**
`ε = (−1)ᵐ` (the count-Lens binary axis, the same `psign`/Legendre/inversion
read of `the_permutation_under_three_readouts`).  Across the prime: the
rank law `α(p) ∣ p − (5/p)` is governed by the Legendre symbol `(5/p)` the
quadratic-reciprocity arc computes — split `p−1`, inert `p+1`, and the
ramified `(5/p) = 0` giving `α(5) = 5`.  The imaginary golden prime read
(`ℚ(ζ₅)`'s real subfield, `C₄`-phase, disc `−4`) and this real golden prime
read (`√5`, Fibonacci `ν₅`, disc `+5`) are the two embeddings of
`ℚ(√5) ⊂ ℚ(ζ₅)`.

## Open frontier

Both bridges named here are now built, ∅-axiom.  The general-`p` rank law
`α(p) ∣ p − (5/p)` is built from the Legendre character
(`DyadicFSM/RankApparition.lean`): the FSM-walking character `legendre213 5 p`
dispatches the entry index `p − (5/p)` (split `p−1`, inert `p+1`, ramified `p`)
and `rank_law_dispatch` gives `p ∣ F_{p−(5/p)}`, each branch through the
universal Fibonacci-mod-`p` machinery.  The shared-`ℚ(√5)` morphism tying the
CP-phase's `ℚ(ζ₅)` reading to the Fibonacci ramification is formalized
(`NumberTheory/GoldenFieldBridge.lean`): the Binet polynomial `x²−x−1` and the
Gaussian-period polynomial `x²+x−1` are one field object under `x ↦ −x`
(`bPoly_neg_eq_gPoly`), sharing discriminant `5` and the single ramified prime
`5` — each a perfect square mod `5` (double roots `3`, `2`; negatives,
`3+2≡0`).  Remaining: the higher-valuation `νₚ(F_n)` rungs for a general prime
(the `p`-tupling analogue of the quintupling identity).
