# What is a polynomial, in 213?

A polynomial is a path whose self-pointing closes: re-reading "how it changes" — the forward
difference `Δ` — terminates at a constant after finitely many steps.  Its degree is that step
count: the number of re-pointings it takes to return to the residue's own constant floor.

## 213-native answer

Take a sequence `s : ℕ → ℤ` — a path one can point at.  `Δ s n = s(n+1) − s n` points again, at how
that path changes; it is a pointing event applied to the trace of the previous pointing, not a new
structure laid on top.  Iterating, `s` is a *polynomial of degree `d`* exactly when the `d`-th
re-pointing stops moving — `liftKZ d s` is constant — and the `(d−1)`-th does not.  That is the
whole content; there is no appeal to "expressions in a variable."  The identity
`Cauchy/DepthCharacterization.finite_depthZ_iff` makes it precise: `polyDepthZ d s ↔ ∃ c, s n =
Σ_{j≤d} C(n,j)·c_j`.  Having finite divergence depth and being a polynomial are the same fact, read
two ways.

## Derivation

The forward direction is reconstruction: a finite-depth path is rebuilt from its leading differences,
`s n = Σ_{j≤d} C(n,j)·(Δʲs)(0)` (`Cauchy/NewtonGregory.reconstruct`).  The reverse is that each
re-pointing-unit *is* a unit of degree: the binomial column `C(·,k)` loses one index under `Δ`
(`diffZ_binomColZ`, Pascal's rule read as a difference), so it returns to the constant `C(·,0)=1`
after exactly `k` steps (`polyDepthZ_binomColZ`); summing columns gives every degree-`d` path finite
depth `d` (`polyDepthZ_newtonZ`).  The count is sharp — the `d`-th difference of a degree-`d` path is
its leading coefficient, `Δ^d (Σ C(·,j)c_j) = c_d` (`liftKZ_newtonZ_const`), so the depth drops below
the degree precisely when that coefficient vanishes (`newtonZ_depth_drop`).  Degree is depth, exactly.

The floor the count descends to is not arbitrary.  The depth-`0` path is the constant difference —
the self-same rule whose step does not depend on `n`.  Its concrete carrier is the cross-determinant
`W = 1` of the `P = [[2,1],[1,1]]` orbit, the Cassini invariant of the Fibonacci/φ path
(`Cauchy/CassiniSigned.cassini_pair`, `Cauchy/DepthResidueFloor`), which `seed/AXIOM/05_no_exterior.md`
§5.6 identifies as the residue's algebraic image: `P(φ) = φ`, self-reference that closes the instant
it is made.  A polynomial of degree `d` is then `d` steps of `n`-dependence away from that pure
self-reference: `e` at 1, `ζ(2)` at 2, `ζ(3)` at 3 (`Cauchy/DepthAperyCubic`).

## Dual function

This is the classical polynomial with its packaging removed: "degree `d`" and "`Δ^{d+1}=0`" are the
same boundary, and the monomial-versus-binomial choice of basis is packaging the difference-count
does not see.  The refinement is where the count comes to rest — 213 relocates "degree" off the
written expression and onto an operational invariant of the path: the number of times re-pointing
must occur before the path coincides with its floor.  A polynomial is not "a thing with coefficients";
it is a path that finitely returns to the self-same rule.

## Cross-frame connections

The closure is one face of a dichotomy that is sharp here because there is no exterior.  A path either
*closes* — finite depth, a polynomial — or it *never closes*: `2ⁿ` and the Liouville numbers have
re-pointing that keeps producing fresh distinction (`DivergenceLadder.infinite_depth`), and "name the
whole act of pointing" reproduces the surplus one level up (`Cauchy/DepthCeilingResidue`,
`Lens.FlatOntologyClosure.object1_not_surjective`).  Infinite depth *is* the residue; finite depth is
the path folding onto itself in finitely many steps — not an exterior reference catching it.  The
same split is `Lens.SelfReferenceThreeOutcomes`: a cross-determinant carries a magnitude that
converges-or-escapes and a sign that toggles with period two, the Nat-converge and Bool-oscillate
readings of one self-pointing (`Cauchy/CasoratianSigned`).  "Closes / never closes," `P(φ)=φ`,
no-exterior, and the converge/oscillate outcomes are one fact at four resolutions.

## Open frontier

Whether a *given* path closes can be undecidable in practice: `π`'s partial-quotient sequence is not
known to be P-recursive, so it is not known to sit at any finite depth on that axis (the
non-holonomicity frontier, `theory/math/analysis/cf_holonomicity_hierarchy.md`).  The characterization
says what finite depth *is*; it does not decide membership for every constructible path.
