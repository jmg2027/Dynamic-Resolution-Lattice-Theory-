# The Frobenius is interior-count collapse

Raising to the `q`-th power, read modulo a prime `q`, becomes **additive**:
`(a+b)^q ≡ a^q + b^q`.  This is not a coincidence of ring axioms — it is a count-Lens reading in
which the *interior* of a binomial expansion collapses to zero, leaving only the two endpoints.

## 213-native answer

The `q`-th power of a sum is a count over interleavings:
`(a+b)^q = Σ_{t=0}^{q} binom q t · a^t b^{q−t}`, where `binom q t` counts the ways to choose `t` of
the `q` factors to contribute an `a` (`Lib/Physics/Simplex/Counts.binom`, Pascal recursion).  Read
this count **modulo `q`**.  Every *interior* coefficient vanishes:

> `q ∣ binom q t` for `0 < t < q` (`Lib/Math/NumberTheory/BinomPrime.prime_dvd_binom`).

So mod `q` the interleaving count is *indistinguishable from zero* everywhere except at the two
endpoints `t = 0, q` (where `binom q 0 = binom q q = 1`).  The power map, read at resolution `q`,
keeps only `a^q + b^q`.  The Frobenius `x ↦ x^q` is exactly this collapse — the additive
homomorphism `add_pow_modEq_prime` (`Lib/.../EisensteinFreshman`) is its statement.

The proof of `prime_dvd_binom` is itself a count identity: the absorption law
`(n+1)·binom n k = (k+1)·binom (n+1)(k+1)` (`succ_mul_binom`) gives `t·binom q t = q·binom (q−1)(t−1)`,
so `q ∣ t·binom q t`; since `q` is prime and `q ∤ t` (`0<t<q`), the count `binom q t` carries the
factor itself.  The vanishing is forced by the prime not by the ring.

## Derivation across carriers — one collapse, three deployments

The same interior-count collapse runs in three places the corpus reaches independently.

**Group ring `R[C_p]` (cubic reciprocity).**  The collapse holds coefficient-wise for convolution,
not just for `ℤ[ω]` multiplication: the convolution binomial theorem `convPow_add_pow`
(`Lib/.../EisensteinConvBinomial`) expands `(f ⊕ g)^{⋆q}`, and the interior terms — each a multiple of
`binom q t` — vanish mod `q`, giving the group-ring Frobenius `convPow_add_pow_modEq_prime`
(`EisensteinConvFreshman`).  Applied to the Gauss sum `g(χ) = Σ_t χ(t)·e_t`, this is the engine of the
cubic Frobenius congruence `g^{⋆q} ≡ χ̄(q)·g (mod q)` toward the reciprocity law
(`math/numbertheory/cubic_residue_and_jacobi_sum.md`).

**`ℤ_p` (Teichmüller).**  The `p`-adic Frobenius and Teichmüller representatives
(`NumberSystems/Padic/{Teichmuller,TeichmullerUnit}`) lift `𝔽_p` exactly because `x ↦ x^p` is the
ring endomorphism the same collapse produces — the unit's Teichmüller character is the fixed locus of
this map.

**Prime counting (Chebyshev/PNT).**  The *other* reading of the same object: instead of asking which
interior coefficients vanish mod `q`, ask how divisible the *central* coefficient is.  The
`v_p(binom 2n n)` bounds drive `∏_{p≤x} p` (`math/numbertheory/chebyshev_prime_counting.md`,
`FactorialRatioBound`).  The Frobenius reads the binomial *row* mod `q` (interior `≡ 0`); prime
counting reads the binomial *valuation* (how many primes a central count absorbs).

## Dual function

Classically this is "the Frobenius endomorphism of a characteristic-`p` ring", proven by "the
binomial coefficients `binom p k` are divisible by `p`."  Strip the ring-theory packaging and the
content is a statement about **counts**: an interleaving count, read at the resolution of its own
prime, retains only its endpoints.  213's refinement is sharper than "the coefficients happen to be
divisible" — the divisibility is the count-Lens reading-out doctrine in force
(`essays/synthesis/zero_valued_quantities_are_readouts.md`): a count read mod `q` lands `0` exactly
where the prime divides it, and the interior of `binom q ·` is precisely that locus.

## Cross-frame connections

The interior-count collapse, the multiplicativity-as-×-count-Lens reading
(`essays/synthesis/multiplicativity_is_the_x_count_lens.md`), and the additive/×-count duality
(`addition_and_multiplication_are_two_faces_of_one_count`) are one family: arithmetic facts are
count-Lens readings, and a prime is the resolution at which its own interior counts become
indistinguishable from zero.  The reciprocity ladder rests on this — the cubic character read as a
discrete-log-mod-3 class (`ModArith/CubicResidue.cube_iff_three_dvd_dlog`) and the quadratic as
discrete-log parity (`DiscreteLogParity`) are the same `kth_power ⟺ k ∣ dlog` collapse at `k = 3, 2`.

## Open frontier

The cubic Frobenius congruence `g^{⋆q} ≡ χ̄(q)·g (mod q)` is not yet assembled — the interior collapse
is proven (`convPow_add_pow_modEq_prime`), but the character-power `χ(t)^q = χ̄(t)` and the
`t ↦ tq` reindex that finish it remain open.  The
unification "one collapse, three deployments" is a refactor target, not yet a single Lean lemma: a
shared `Frobenius-from-interior-binomial-vanishing` over an arbitrary carrier would make the cubic,
`p`-adic, and prime-counting uses literal corollaries of `prime_dvd_binom`.
