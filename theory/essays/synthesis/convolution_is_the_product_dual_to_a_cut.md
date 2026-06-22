# A convolution is the product dual to a cut

A convolution is the operation that **multiplies two sequences by summing over every way
to cut the index** — `(f ⋆ g)(n) = Σ_{(a,b) : a∘b = n} f(a)·g(b)`, where `∘` is whichever
composition (addition or multiplication) generated `n`. The convolution is the product;
the *cut* — the co-operation that enumerates the decompositions `a∘b=n` — is the object it
is dual to.

## 213-native answer

Fix a composition law `∘` on ℕ. Its **cut** is the comultiplication `Δ_∘(n) = {(a,b) :
a∘b = n}`, an explicit, residue-internal listing of the ways `n` was reached. For
addition, `Δ_+(n) = natSplits n = [(0,n),(1,n−1),…,(n,0)]`
(`Meta/Nat/Convolution213.lean`); for multiplication, `Δ_×(n) = {(d, n/d) : d∣n}`
(`Lib/Math/NumberTheory/DirichletIdentities.lean`). The convolution dual to `∘` weighs each
cut by `f` on the left part and `g` on the right and sums:

- **additive cut → Cauchy convolution** `conv f g n = Σ_{i+j=n} f i·g j` — generating-function
  multiplication;
- **multiplicative cut → Dirichlet convolution** `dconv f g n = Σ_{d∣n} f d·g(n/d)` — the
  divisor convolution.

The pair (cut, weighted sum) IS the convolution. There is no separate "multiplication of
power series" hovering above; the multiplication is exactly the act of enumerating the cuts
and summing the products (`conv`'s definition is literally `sumMap` over `natSplits`).

## Derivation

That the convolution *is a product* — associative, commutative, unital — is not an extra
axiom; it is **inherited from the cut's symmetries**. `conv_comm` is the cut-reversal swap
`(i,j)↦(j,i)` on `natSplits`; `conv_assoc` is the **coassociativity** of the cut — cutting
`n` into three pieces two ways enumerates the same `{(i,j,k):i+j+k=n}`
(`theory/math/combinatorics/convolution_generating_functions.md`). The unit `δ=[1,0,0,…]`
is the cut's counit: only the degenerate cut `(0,n)` survives (`conv_delta_left`). The same
mechanism on the multiplicative cut gives the Dirichlet ring its commutativity and
associativity, with `μ∗1=ε`, `φ=μ∗id`, `σ_k=id^k∗1`, the Jordan totient `J_k=μ∗id^k`
(`multiplicative_divisor_theory.md` §9). So "convolution is a commutative monoid product" is
a *shadow of a comultiplication swap symmetry* — the same doctrine that makes `+` commute
(`UnitList.append_comm`) and `×` commute (`UnitGrid.mul_comm_from_grid`), now read one scale
up, on sequences.

The cut also explains *why* the convolution computes what it computes. `conv ones` is the
discrete antiderivative (`conv_ones_prefixSum`: convolving with the constant `1` sums the
prefix) because `Δ_+` lists exactly the prefixes; `conv (brow a)(brow b) = brow(a+b)`
(Vandermonde) because cutting `a+b` choices into an `a`-part and a `b`-part is what the
binomial coefficient counts. Möbius inversion is the statement that `μ` is the `Δ_×`-inverse
of `1` — invert by reading the multiplicative cut backwards.

## Dual function

This is the classical Cauchy/Dirichlet convolution — and the coalgebra/Hopf-algebra
account of why generating-function multiplication is associative — with the
completed-coalgebra packaging stripped: no `Finset.sum` machinery (which imports `propext`),
no ambient ⊗ over a base ring, just the explicit finite list `Δ_∘(n)` and a fold, ∅-axiom
(`#print axioms conv_assoc` empty). The refinement 213 adds is that the convolution's
algebraic laws are *not postulated and not borrowed from the coefficient ring*; they are
**derived from the cut's own swap/reglue symmetries**, so the comultiplication, not the
product, is the primitive object. The reading "split IS a `+`-witness" makes `Δ_+` the
inverse-question co-operation (how was `n` reached?), and the convolution its dual closure.

## Cross-frame connections

ℕ carries two cuts, `Δ_+` and `Δ_×`, and they are the object-level home of the function-level
fact essayed in `addition_and_multiplication_are_two_faces_of_one_count` and
`multiplicativity_is_the_x_count_lens`: a function is **multiplicative** exactly when it is a
`Δ_×`-coalgebra morphism (respects the multiplicative cut on coprime parts, `dconv_mul`,
coprimality = disjoint-support of the cut), and `vp` is the homomorphism intertwining the
two cuts (`vp_mul`: `Δ_×` becomes addition of exponent vectors). Convolution-product /
cut-comultiplication / count-Lens-with-two-faces — the same fact at three resolutions: the
product, its dual co-operation, and the readout that carries one cut to the other.

## Open frontier

The two cuts are not independent — `×` distributes over `+`, so `Δ_+` and `Δ_×` should
satisfy a bialgebra compatibility. The sharp open target: **binomial inversion (the additive
antipode, `A n g = Σ(−1)^k C(n,k) g(k)`, `inclusion_exclusion_set_partitions.md`) and Möbius
inversion (the multiplicative antipode) are two faces of one antipode under the two cuts** —
both sides closed in the corpus, the unifying statement supplied by
`incidence_inversion.md` (the antipode as one construction read through `Δ_+`/`Δ_×`).
