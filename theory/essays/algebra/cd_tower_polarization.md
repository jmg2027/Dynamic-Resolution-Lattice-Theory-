# The Cayley-Dickson algebra tower over 213 — the polarization condition

Each rung of the tower is one syntactic operation: `CDDouble α = α × α`
with `(a,b)·(c,d) = (a·c − conj d·b, d·a + b·conj c)` and
`conj(a,b) = (conj a, −b)`.  The "tower" is this single arrow iterated;
nothing is added at any rung
(`lean/E213/Meta/Algebra213/CDDouble.lean`; `math/cayley_dickson/algebra_tower.md` §1).

## 213-native answer

The tower is not a sequence of ever-bigger number systems.  It is the
orbit of one doubling-arrow under iteration, and each application is a
residue that commits to strictly **fewer** equations than its operand.
Which equations survive is fixed by two Lens readouts of the residue —
a quadratic one `a·conj a = ofInt(normSq a)`
(`Core.lean`, `IntegerNormed213.self_mul_conj`) and its linear companion
`a + conj a = ofInt(trace a)`
(`Core.lean`, `TraceNormed213.self_add_conj`) — not by the carrier's
size.  These two are the coefficients of `x² − trace(a)·x + normSq(a)`,
the minimal polynomial of a Hurwitz integer.

## Derivation

Norm composition `|u·v|² = |u|²·|v|²` is the property that "wants" to
survive each doubling.  Over a commutative base it survives trivially;
over a non-commutative **associative** base (Lipschitz → Cayley =
integer octonions) it still holds, but the degree-4 Hurwitz expansion no
longer collapses by associativity.  The expansion splits cleanly: four
**diagonal** terms become central `ofInt` scalars via `self_mul_conj`,
and four **cross**-terms — the genuine non-commutative residue
`conj a·conj w − conj w·conj a = a·w − w·a` — cancel *exactly because*
`a + conj a` is central.  That cancellation is `cross_zero`; the
assembled identity is `hurwitz_norm_re`, yielding `cd_normSq_mul` for any
`[TraceNormed213 α]` (`Meta/Algebra213/CDDoubleMoufang.lean`).  The same
trace-centrality discharges octonion alternativity: `cd_alt_left`, then
`cd_alt_right` by the conj anti-automorphism, then `cd_flexible` by
linearization (`Meta/Algebra213/CDDoubleAlternative.lean`).  So the
polarization condition — the linear trace form paired with the quadratic
norm — is the precise structural content of "octonions are the last
composition algebra."

## Where it stops

One rung higher (Cayley → Sedenion = `CDDouble` of a **non-associative**
base) the trace condition no longer lifts and composition fails —
concretely: `(e₁+e₁₀)·(e₄−e₁₅) = 0` with both factors nonzero, so
`normSq(u·v) = 0 ≠ 4 = normSq u · normSq v`
(`Lib/Math/Algebra/CayleyDickson/Levels/SedenionZeroDivisor.lean`:
`sedenion_has_zero_divisors`, `sedenion_normSq_not_multiplicative`).
The boundary is not asserted; it is a `decide`-witnessed 16-tuple.

## Dual function

This is the classical Cayley-Dickson tower with its packaging stripped:
"the tower loses a property at each step" reads operationally as "each
doubling-arrow is a residue committing to fewer equations, and which
survive is fixed by two Lens readouts, not by dimension."  213's reading
is sharper at the boundary — the place composition stops is not a
dimension count (8 vs 16) but the failure of the linear trace form to
stay central under a non-associative operand, and that failure is
exhibited by pointing at a specific 16-tuple rather than argued.

## Cross-frame connections

The same fact appears in three frames.
  (i) **Quadratic/linear pairing**: `self_mul_conj` (norm) and
      `self_add_conj` (trace) are the two minimal-polynomial
      coefficients; the cross-term cancellation is the polarization of
      the quadratic into its bilinear companion.
  (ii) **φ frame**: each type's Moufang-failure rate converges as
      `1 − (1/2)·(1/φ)^rank`, φ = (1+√5)/2 the minimum fixed point of
      self-reference (`seed/AXIOM/05_no_exterior.md` §5.6); the rung
      where composition dies is the rung where that rate first becomes
      positive.
  (iii) **No-exterior**: there is no outside dialer choosing where the
      tower stops — the stopping point is forced internally by which
      Lens readout stays central, exactly as
      `seed/AXIOM/05_no_exterior.md` §5.1 requires.

## Open frontier

Flexibility `(u·v)·u = u·(v·u)` survives *all* the way up — even
Sedenion is flexible — unlike composition.  Its 213 proof over a
non-associative base is not closed: the foundation (`FlexAlt213` +
`flex_polar` + the trace/sandwich lemmas, all ∅-axiom in
`Meta/Algebra213/CDDoubleFlexible.lean`) is in place, but the cross-pair
identity that would close `cd_flexible` is `flex_polar`- and
conj-self-similar and resists the trace-centrality reduction that closed
composition (see `HANDOFF.md` for the precise reduction state).  So the
"which property survives how far" picture is verified for commutativity /
associativity / alternativity / composition, and open for the
flexibility rung past Cayley.
