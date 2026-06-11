# Slot tower ↔ main — cross-domain insights

Where this branch's slot-tower arc (`append→+→×→^`, the `^`-wall, the
`vp_separation` keystone, the fold criterion, the order-loss theorem) meets
what main brought in (LambertWeld, discrete Perelman/Ricci, `OrderMul`, the
"two pointings are one" essay).  Plain statements; pins to the Lean both
sides.  Open until a bridge theorem is written.

## 1. Equality is a certificate, and the certificate has a shape

Main's `when_two_pointings_are_one` (the weld essay): with no enclosing
line, "two pointings name the same real" is exactly as strong as the
combinatorial certificate that proves it — and the certificate has a *size*
(the per-level Padé flip, `48` at level one) and a *shape*
(presentation-shaped: the Lambert CF's linear partial-quotient growth).

This branch's `FoldCriterion.pow_eq_pow_iff_vp`: two powers are equal iff
their prime-exponent readings match at every prime.  That iff *is* a
certificate for "two numbers are equal" — and its content is the prime
structure (`vp`-vectors), licensed by `vp_separation` (the readings
determine the number).

**One shape, two domains**: equality is never free; it is a checkable
certificate, and the certificate's content is the structure of the object
(CF level for the weld real, prime exponents for the power).  Bridge to
write: state "equal ⟺ certificate matches" as one schema with the weld and
the power as two instances.

## 2. Order ⟺ no wrap (exact duals, both now proved)

Main's `Int213.OrderMul` (sign trichotomy): ℤ carries a translation-
invariant order — every nonzero integer is `> 0` or `< 0`.  This branch's
`NoOrderModP.no_wrapping_order`: the circle `1..p` carries *no* such order
(adding 1 walks back to the start, forcing `1 < 1`).

These are the **two sides of one fact**: a translation-invariant order
exists exactly when the structure does not wrap.  ℤ is the un-wrapped
counting line extended by sign and keeps the order; `mod p` folds the line
into a circle and loses it.  This is the price the `^`-wall's escape route
pays: you *can* fold into `mod p` to make every power solvable (discrete
logs always exist on a cyclic group), but the order the line had is gone.
Bridge: "order on `M` ⟺ `M` is wrap-free", with ℤ (yes) and `ℤ/p` (no) the
two instances.

## 3. The exp / log boundary: tame one way, wild the other

Main's LambertWeld: `exp(2/q)` and `coth(1/q)` of a rational are reachable
as tame cuts — the Lambert continued fraction has *linear* partial-quotient
growth, so the pointing is hypothesis-free (`weld_closed`, unconditional).

This branch's `^`-wall (`FoldCriterion.fold_iff_collinear`): `aˣ = b` for
incommensurable `a, b` (exponent-vectors not parallel) has no finite-tuple
answer — its solution (a logarithm) is the cut that does *not* fold back.

**Same boundary, two sides**: exponentiating a rational is *tame* (Lambert,
a clean cut), taking a logarithm across two different prime axes is *wild*
(the wall, a non-folding cut).  LambertWeld is the exp-half, FoldCriterion
the log-half, of the one exp/log story.  Bridge: place both on the
fold-back map — exp(ℚ) folds (tame CF), log of non-collinear primes does
not (the wall) — and ask what exactly separates the tame cuts from the wild
ones (CF growth rate vs exponent-vector independence; the weld essay's
"linear partial-quotient growth" is the tame marker).

## 4. The substrate's shape: metric facet vs topological facet

This branch's `Shape213` / `GridReadout213`: raising the substrate
dimension makes the readout vector-valued — but the honest internal readout
is the *shape* (an ordered factorization), and dimension = number of
factors; the metric dressings (area, perimeter) were the import to drop.

Main's discrete Perelman / Ricci core (`discrete_perelman_core.md`,
curvature stencils): the genuinely presentation-invariant version of "the
substrate has structure beyond a single count" is *topological* —
curvature, Euler characteristic, the Ricci flow programme.

**One knob, two readings**: "the substrate has shape" is read *metrically*
by the factorization/grid (this branch) and *topologically* by curvature
(main).  The curvature-as-Lens-readout essay (synthesis IV) already says
curvature is a difference-Lens count + sign; the bridge here is that the
factorization-shape and the curvature-shape are two readouts of the same
"a count is not enough once the substrate has more than one axis".

---

All four are **open bridges** (the cross-domain claim is plain; the
single-schema Lean statement is not yet written).  Recorded so the
correspondence is tracked, not lost to chat.
