# Multiplicativity is the ×-count-Lens reading through its axes

A function `f : Nat → A` is **multiplicative** when it is a readout of the
×-count-Lens that factors through the per-prime-power axes: `f` is fixed by
its values `f(p^a)` on prime powers, and `gcd(m,n)=1 ⟹ f(mn)=f(m)f(n)` because
the exponent vectors of coprime `m,n` have disjoint support.

## 213-native answer

Point `n` at the **×-count-Lens** — the multiplicative reading that records, for
each prime `p`, how many times `p` divides `n`. The readout is the exponent
vector `(v_p(n))_p` (`Meta/Nat/Valuation.vp`). This vector is *faithful*: distinct
`n` give distinct vectors (`Meta/Nat/VpSeparation.vp_separation`, ∅-axiom). So `n`
**is** its exponent vector under this Lens — nothing about `n`'s multiplicative
structure is lost or added.

A function is multiplicative exactly when it is a function *of that vector,
axis by axis*: `f(n) = ∏_p f(p^{v_p(n)})`, with the axes independent. The
coprimality hypothesis `gcd(m,n)=1` is not an extra condition bolted on — it is
the syntactic statement that the supports of `(v_p(m))_p` and `(v_p(n))_p` are
disjoint, so the vector of `mn` is the concatenation and the product splits:
`f(mn)=f(m)f(n)`.

## Derivation

The reading is built, not assumed. `DivisorMultiplicative.divisor_product_reindex`
proves, for coprime `a,b`, the sparse-fiber reindex `divisorSum (a·b) f =
Σ_{i<a}Σ_{k<b} dvdInd i a · dvdInd k b · f((i+1)(k+1))` (on the grid form
`DivisorProductReindex.divisorSum_mul_as_grid`) — the divisors of a coprime
product are the *product* of the divisor sets, which is the axis-independence
made combinatorial. Riding that reindex, `DivisorMultiplicative.sigma_mul` /
`tau_mul` and `GeneralizedDivisorSum.sigmaK_mul` (all `k`) are multiplicative;
the whole family (`theory/math/numbertheory/multiplicative_divisor_theory.md`)
is determined by its prime-power values.

Squareness is the same Lens read as a parity: `n` is a perfect square ⟺ every
axis is even. `SquareCharacterization.isSquare_iff` splits this at the prime 2
(`IsSquare n ↔ v2 n even ∧ IsSquare (oddPart n)`) via the general,
UFD-free `coprime_isSquare_mul` (coprime `u,v ⟹ IsSquare(uv) ↔ IsSquare u ∧
IsSquare v`) — a *property* riding the same axis-independence a multiplicative
*function* rides. The parity capstone `SigmaParityComplete.sigma_odd_iff`
(`σ(n)` odd ⟺ `n` square or twice-square) is the multiplicative readout
`σ(p^a) ≡ a+1 (mod 2)` summed across the faithful vector.

## Dual function

This is the classical pair "multiplicative function + fundamental theorem of
arithmetic," with the packaging stripped. Classically the FTA is a separate
theorem you invoke to justify "define `f` on prime powers and extend." Here the
FTA is not invoked — it *is* `vp_separation`, the statement that the ×-count-Lens
is faithful; and "multiplicative" is not a property you check against the FTA but
the prior fact that `f` is a readout of that Lens. The sharper 213 reading: a
multiplicative function carries no information beyond its restriction to one axis
at a time, because the residue under the ×-count-Lens already *is* the
independent-axis vector — the extension is identity, not construction.

## Cross-frame connection

Why does multiplicativity exist at all? Because **×-atoms are distinguishable
where +-atoms are not.** Additively, every atom is the same unit `1`: the
+-atom list collapses under reordering (`UnitList.append_comm`), so the additive
readout has *one* axis and degenerates to magnitude = count. Multiplicatively,
the atoms are the distinct primes, so the ×-readout is a *vector* over
distinguishable axes (the `^`-wall: the inverse of `aˣ=b` is decided in ℕ by
whether the prime charts are parallel, `TwoThreeUnique.two_three_unique`).
Multiplicativity is precisely the structure a function can have *because the
multiplicative atoms carry distinct identities* — it is the function form of
×-atom distinguishability, the exact dual of the indistinguishability that
makes addition have no analogous "additively multiplicative" functions. Same
residue, two Lenses: one atom (addition) versus many distinguishable atoms
(multiplication).

## Open frontier

That the ×-count vector is faithful (`vp_separation`) is proven; that an
arbitrary multiplicative function's *value* is forced by descent over the
factorization is instantiated (`SigmaParityComplete.sigma_odd_square_odd`, by
smallest-prime-power induction) but not yet abstracted into a single "any
multiplicative function descends over the UFD vector" schema — recorded in
`research-notes/frontiers/crossdomain_divisor_x_branch_merge.md` as a candidate
member of the iterated-descent catalogue. Whether "multiplicative-function
descent" is its own rung or the UFD descent read through the counting Lens is
open.
