# Cross-domain insights — this branch's closures × main's existing framework (2026-06-18)

Main was fully contained in the branch (0 ahead at merge), so "main" = the established base
(divisor theory, FLT/Freshman, Mobius213/SL₂, Heron, valuation/`vp_separation`) and "branch" =
this session's new closures (LTE, σ_m, Euclidean-lattice geometry, two-variable binomial theorem).
Genuine links, recorded as they came to mind:

## 1. LTE is the exact-valuation *lift* of Freshman's dream — same `p ∣ C(p,k)`

Main's `DyadicFSM/FLT/FreshmanDream` proves `(a+b)ᵖ ≡ aᵖ + bᵖ (mod p)` from `p ∣ C(p,k)`
(`0<k<p`).  Branch's LTE kernel (`lifting_prime_power`) uses the **same** `prime_dvd_choose` for
its tail bound `v_p(R) ≥ v_p(d)+2`.  The relationship is exact: Freshman = the statement *mod p*
(first order — the binomial tail vanishes mod p); LTE = the statement to *all orders* (the exact
valuation of the difference).  **LTE is Freshman's dream read by the full count-Lens instead of
its one-bit `mod p` truncation.**  Both are `p ∣ C(p,k)` cashed at different resolutions.

## 2. The ultrametric strict-min law is the additive dual of multiplicativity-as-×-count-Lens

The essay `multiplicativity_is_the_x_count_lens` (main) states: a function is multiplicative ⟺ a
readout of the ×-count-Lens (`vp`, faithful by `vp_separation`).  Branch's `vp_add_eq_min`
(`v_p(x)<v_p(y) ⟹ v_p(x+y)=v_p(x)`) is the **additive** behaviour of the same `vp`: where
multiplication *adds* exponents, addition takes the *minimum* (strictly, when unique).  LTE needs
both faces of `vp` at once — additivity over the product factorization and the strict-min over the
binomial sum.  The "lifting" phenomenon is literally the count-Lens tracking how the difference
operation shifts the exponent: `v_p(aⁿ−bⁿ)` decomposes into the base shift `v_p(a−b)` plus the
exponent's own count `v_p(n)`.

## 3. σ_m's general law instantiates the divisor-theory essay's open frontier (partially)

The `multiplicativity_is_the_x_count_lens` essay's open frontier was "any multiplicative function's
value is forced by descent over the UFD vector — instantiated but not abstracted."  Branch's
`divisorSumZ_mul_of_completely_mult` is a concrete step toward that abstraction: it proves the
**divisor-sum operator** preserves multiplicativity for *any* completely-multiplicative weight in
one theorem (σ/τ/σ_m all become corollaries).  Still not the full "any multiplicative function"
abstraction, but it collapses the previously per-function multiplicativity proofs (`sigma_mul`,
`tau_mul`, `muStruct_divisorSum_mul`) into one.

## 4. SL₂(ℤ) lattice-area invariance is the geometric root of main's Mobius213 modular action

Main has a large Mobius213 / Stern–Brocot / Markov / continuant programme — the modular group
`SL₂(ℤ)` acting on fractions/continued-fractions.  Branch's `area2_unimodular`
(`det=1 ⟹ area2(MA,MB,MC) = area2(A,B,C)`) is the **same `det=±1` invariance read in the geometry
Lens**: the modular group preserves the lattice's signed area.  The number-theoretic action (on
Stern–Brocot mediants, `det`-1 neighbour pairs) and the geometric action (lattice-area-preserving)
are one `det` invariant under two Lenses — a clean "one Raw, two Lens" instance.

## 5. Cayley–Menger is Heron made √-free (the determinant form is the 213-native one)

Main's `Foundations/HeronFormula` gives `16·Area² = …` via symmetric polynomials of the side
lengths.  Branch's `LatticeArea.cayley_menger` gives `16·Area² = 4·AB²·AC² − (AB²+AC²−BC²)²` via
the Gram determinant `area2² = AB²AC² − (dot)²` + law of cosines.  Same classical content; the
**determinant/squared-distance route is the 213-native one** because it never leaves `ℤ` (no √),
whereas the side-length route implicitly carries the irrational distances.  This is the geometry
instance of the recurring "work with the squared/cut-internal quantity, not the irrational
pointing" doctrine (`External-ruler smuggling` / `Transcendental-as-exterior` failure rows).

## 6. Meta-craft: the abstract-atom decomposition surmounts the `ring_intZ` degree-ceiling

A transferable ∅-axiom-craft yield, not a math theorem: high-degree polynomial identities that
time out `ring_intZ` (Cayley–Menger, degree 8) close by **decomposing through intermediate named
quantities held as opaque atoms** (2D-Lagrange deg 4 + law-of-cosines deg 2 + abstract assembly).
The same shape appears in LTE's `vp_add_eq_min` (the binomial sum is split into middle + tail, each
analyzed abstractly).  Pattern: *when a reflective tactic hits its complexity wall, factor the goal
through abstract intermediates — the wall is on raw expression size, not on the mathematics.*
