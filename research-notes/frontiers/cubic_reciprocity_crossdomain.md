# Cross-domain insights — the cubic-reciprocity branch ↔ the main corpus

Connections between this branch's cubic / Eisenstein reciprocity work (Phase A `N(J)=p` + the
group-ring Frobenius engine) and disciplines already in `main`.  Each names the **shared engine**, not
a surface analogy.

## 1. The group ring `R[C_p]` convolution **is** the generating-function / comultiplication convolution

This branch builds `conv p f g k = Σ_{i<p} f(i)·g((k−i) mod p)` (`EisensteinGroupRing.conv`) and a
full convolution binomial theorem (`EisensteinConvBinomial.convPow_add_pow`) coefficient-wise.  That
is the **same** convolution as main's generating-function multiplication
(`theory/math/combinatorics/convolution_generating_functions.md`, `Meta/Nat/Convolution213`) and the
dual of comultiplication (`convolution_comultiplication_crossdomain.md`).  The cubic Gauss-sum
Frobenius therefore lives in the algebra main already studies — only the carrier ring is `ℤ[ω]` and
the group is `C_p` (cyclic) rather than `ℕ` (free monoid).
**Actionable:** the convolution-power lemmas built here (`conv_sumRange_left`, `convProd_mul_{f,g}`,
`convPow_scalar`, `basis_conv`: `e_a⋆e_b = e_{(a+b)%p}`) are the `C_p`-graded instance of the generic
convolution algebra — lift them to a shared `conv`-over-a-monoid module rather than re-proving per
carrier.

## 2. The freshman's dream **is** the Frobenius shared with the p-adic / Teichmüller work

`(a+b)^q ≡ a^q + b^q (mod q)` (`EisensteinFreshman.add_pow_modEq_prime`) and its convolution form
(`EisensteinConvFreshman.convPow_add_pow_modEq_prime`) are the **Frobenius endomorphism mod `q`**.
Main already runs Frobenius/Teichmüller p-adically (`NumberSystems/Padic/{ZpSqrtDFrob,Teichmuller,
TeichmullerUnit}`).  Same structure: a char-`q` ring homomorphism arising because the interior
binomial coefficients vanish.  The cubic Gauss-sum congruence `g^{⋆q} ≡ χ̄(q)·g (mod q)` is the
`R[C_p]` instance; the Teichmüller lift is the `ℤ_p` instance.
**Actionable:** unify on one "Frobenius from interior-binomial-vanishing" lemma; both deployments are
corollaries of `BinomPrime.prime_dvd_binom` + a binomial theorem over the respective carrier.

## 3. `q ∣ binom q t` (the Frobenius crux) **is** the prime-in-binomial fact behind Chebyshev/PNT

`BinomPrime.prime_dvd_binom` (`q ∣ binom q t` for `0<t<q`, via the absorption identity) is the crux
of the Frobenius here.  The **same** prime-divides-binomial structure drives main's central-binomial
valuation bounds in `theory/math/numbertheory/chebyshev_prime_counting.md` /
`FactorialRatioBound` (`v_p(binom 2n n)` controls `∏ p`).  Two readings of one object: the *Frobenius*
reading (interior row `≡ 0 mod q`) and the *counting* reading (`v_p` of the central coefficient).
**Actionable:** the 213-native `binom` (`Simplex/Counts`) + `succ_mul_binom` absorption identity built
here is the missing reusable substrate for Kummer/Lucas-style valuations of binomials main's
prime-counting work currently re-derives ad hoc.

## 4. `N(J) = p` **is** the Eisenstein (disc −3) analogue of the two-squares norm `p = x²+y²`

The Jacobi-sum norm law `J·J̄ = p` (`EisensteinJacobiNormLaw.jacobi_norm`) represents `p` by the
Eisenstein norm form `N(a+bω) = a² − ab + b²`.  This is the disc −3 sibling of main's two-squares
representation `p = x²+y²` (`FourSquareSeed`, `two_square_only_if.md`, `ℤ[i]` disc −4).  The cross-
domain content: the Jacobi sum **constructs** the representation (`x = Re J`, `y` from `Im J`), the way
the descent/Thue step constructs `x²+y²` — both are "exhibit `p` as a norm in an imaginary quadratic
PID of class number one" (`h(−3)=h(−4)=1`, cf. `eisenstein_period_arithmetic.md`).
**Actionable:** state the shared interface — "norm form of a class-number-one imaginary quadratic order
represents exactly the split primes" — with `p=x²+y²` and `N(J)=p` as the two instances.

## 5. The cubic character as **discrete-log mod 3** mirrors the quadratic character as **discrete-log parity**

`ModArith/CubicResidue.cube_iff_three_dvd_dlog` reads the cubic character as the mod-3 class of the
discrete logarithm; main's `DiscreteLogParity` reads the quadratic (Legendre) character as the
discrete-log *parity* (mod 2).  Same engine (`pow_one_iff_ord_dvd` + `k·m`-divisibility collapse),
index `2 → 3`.  The reciprocity ladder (`quadratic_reciprocity.md` closed, cubic Phase-A closed)
shares the discrete-log-mod-`k`-class skeleton.
**Actionable:** the `three_mul_dvd_iff` / `two_mul_dvd_iff` pair is one lemma at general `k` — a
`kth_power_iff_k_dvd_dlog` would serve every higher-reciprocity character at once.

## Phase B (the cross-modulus synthesis, now closed) — three more

## 6. The μ₃ lift **is** residue separation by a coprime modulus — the count-Lens distinguishability dial

`EisensteinMu3Lift.mu3_eq_of_modEq_pi`: two distinct cube roots of unity differ by an element of norm
**3** (`‖ω−1‖²=‖ω²−1‖²=‖ω²−ω‖²=3`), so any prime `π` of norm coprime to 3 keeps them distinct mod `π` —
a μ₃ *congruence* is forced to be an *equality*.  This is the **same** structure as the quadratic μ₂
lift (distinct square roots differ by `2·unit`, separated by odd moduli) and, generically, as CRT
residue separation: a finite value group `μ_k` injects into `ℤ[ω]/(π)` exactly when `N(π)` is coprime to
the discriminant of the value group's difference set.  213-native: the modulus is a **resolution**, and
"coprime to 3" means the resolution is fine enough to *distinguish* the three roots —
`distinguishability_is_the_one_dial` at the value-group scale (the dual of the +-atom indistinguishability
that collapses the *interior* counts in #2/#3).
**Actionable:** one `muK_eq_of_modEq` lemma at general `k` — value group `μ_k`, difference-set
discriminant `k` (resp. its odd part), separated by any modulus coprime to it — subsumes the μ₂ (Legendre)
and μ₃ lifts and every higher one.

## 7. The conjugate-modulus flip **is** the involution/Galois readout — Cayley–Dickson conjugation, Hodge ⋆⋆

`EisensteinConjModEq.conj_modEq`: `A ≡ B (mod d) ⟹ conj A ≡ conj B (mod conj d)` — conjugation carries a
congruence to the **conjugate** modulus; it does *not* fix the modulus.  This is the nontrivial element of
`Gal(ℚ(ω)/ℚ)` permuting the two primes `π ↔ π̄` above `p`, and the load-bearing correction of the whole
synthesis: a split prime's residue field `ℤ[ω]/(π') ≅ 𝔽_{p'}` is the **prime** field, which has *no*
nontrivial automorphism — so conjugation must *leave* it (`ℤ[ω]/(π') → ℤ[ω]/(π̄')`), which is why the
source's "conjugate law" `χ_π(ᾱ)=conj χ_π(α)` is false and the honest law flips the modulus.  The same
involution `conj` is the **Cayley–Dickson conjugate** (`ZOmega.conj`, the disc−3 floor of the CD tower
`math/cayley_dickson/`) and the abstract sibling of the **Hodge ⋆⋆=id** involution
(`cohomology/hodge.md`): an involution on an ambient ring need not descend to a quotient — when it does
(inert `q`: conj = the `q`-Frobenius of `𝔽_{q²}`) vs when it cannot (split `π'`: conj exits the field) is
exactly the inert/split dichotomy.
**Actionable:** state "an ambient involution descends to `R/(d)` iff `d` is `conj`-stable (associate of
`conj d`)"; the inert/split cases of cubic reciprocity are the two branches, mirroring the
ramified/split/inert trichotomy of `eisenstein_period_arithmetic.md`.

## 8. Reciprocity collapses to a **finite abelian-group identity** — algebraic priority over continuity

`EisensteinCubicReciprocitySplit.mu3_reciprocity_algebra`: the entire split law reduces to a `3⁴`-case
identity in the group `μ₃` (`C=conj E·A² ∧ E=conj C·S² ⟹ A=S`, proven by `decide`).  No analysis, no
limit — a finite check, the **algebraic-priority** thesis (`CLAUDE.md`: DRLT results come from counting,
not continuous variation) made literal: a "deep" reciprocity law *is* a finite-group fact.  Same shape as
**Zolotarev** (quadratic reciprocity = a permutation **sign**, `zolotarev.md`) — both reduce reciprocity
to a finite-group invariant (sign in `S_n` / element of `μ₃`), forced by a **symmetry** of a paired
construction (the swap `π ↔ π'` gives the two relations whose symmetric solution is `A=S`).  The
Gauss-sum → Jacobi-sum → finite-`μ₃`-cancellation pipeline is the disc−3 instance of "transcendental-looking
sum, finite-group answer."
**Actionable:** the reciprocity symmetry is a fixed point of the prime-swap involution on the pair of
relations; a general "symmetric pair of `μ_k` relations ⟹ equal symbols" closer would serve cubic, and
(with `μ₄`) quartic, reciprocity.

---

*Status: open cross-domain board.  None of these is a Lean theorem yet; each is a refactor/unification
target.  Phase-A convergences: #1 (one convolution algebra), #2+#3 (one Frobenius crux `prime_dvd_binom`
serving p-adic, cubic, prime-counting).  Phase-B convergences: #6 (one `μ_k` separation lemma), #7 (the
involution-descends-iff-modulus-stable dichotomy = inert/split), #8 (reciprocity = a finite-group
invariant, shared with Zolotarev's sign).*
