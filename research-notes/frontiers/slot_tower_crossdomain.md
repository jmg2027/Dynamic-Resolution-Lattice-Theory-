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

**Size half made precise (power side).**  `FoldCriterion.pow_eq_pow_iff_vp_support`
sharpens the iff: the check runs only over the *finite* support
`{p prime : p ∣ a ∨ p ∣ b}` — outside it both readings vanish and the check
is automatic.  So the power-side certificate has an explicit, finite size
(the divisor primes, each `≤ a` or `≤ b`), matching the weld's "the
certificate has a *size*" (per-level Padé flip).  Both certificates are a
`∀`-over-resolution-levels local check — the weld indexed by truncation `J`
(`weld_pair_cosh/sinh` hold at every `J`), the power by support prime `p`.

**Still open — the single cross-domain schema.**  "equal ⟺ certificate
matches" as one Lean object with the weld and the power as two instances is
*not yet written*, and is not a quick win: the two certificates are indexed
by **different resolution types** (truncation level `J` vs. support prime
`p`), so the only literal shared abstraction is the near-trivial
"`∀ level, local check`".  A non-vacuous unification needs a genuine shared
*mechanism* (as bridge 2's orbit-walk obstruction is), not just a shared
`structure { cert : Prop, iff : eq ↔ cert }` — writing the latter would be a
forcible map.  The shared narrative is already carried by
`theory/essays/synthesis/equality_is_a_certificate.md`; the open task is to
find the mechanism, not to restate the narrative in Lean.

## 2. Order ⟺ no wrap (exact duals) — **CLOSED**, single schema written

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

**Bridge written** (`lean/E213/Meta/OrderWrap.lean`, 9 PURE).  A successor
structure `(M, s, a)` carries an `OrderWitness` (irreflexive + transitive +
`s`-equivariant + seed edge `a < s a`).  The single schema is the
obstruction:

* `no_order_of_wrap` — if the orbit `a, s a, s²a, …` returns to `a` after
  `n > 0` steps, **no** `OrderWitness` exists (walking the seed edge reaches
  `a < a`).

Two instances of the one schema:

* **ℤ** (`s = (·+1)`, `a = 0`): `intOrderWitness` exhibits the order, and
  `int_orbit_no_wrap` shows `orbit n = n ≠ 0` for `n > 0` — no wrap, so the
  schema produces no contradiction and the order survives.
* **ℤ/p** (`s = next p`, `a = 1`): `modp_no_order` — the orbit wraps
  (`orbit p = 1`), so the schema rules out every witness, re-deriving
  `no_wrapping_order` as a corollary.

So "order on `M` ⟺ `M` is wrap-free" is now one Lean object with ℤ (yes) and
`ℤ/p` (no) as the two readings.

## 3. The exp / log boundary: tame one way, wild the other — narrative only (formally disjoint)

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

**Verdict (this session): no single schema — narrative only, formally
disjoint.**  The tame side has *no formalised "growth rate" object*: the
linear partial-quotient growth `(2n+1)q` is baked into the fixed arithmetic
coefficients of the weld recursion (`weld_ladder`, `cf_bridge`), not a
studied quantity.  The wild side (`fold_iff_collinear`) is exponent-vector
collinearity over primes — a finite-support existence check with no
continued-fraction structure.  No theorem links a CF partial-quotient growth
rate to prime-exponent collinearity, and the two objects live in disjoint
parts of the build (Real213 cuts vs Meta/Nat valuations).  A unifying Lean
statement would pair CF-recursion depth with a factorization existence check
with no shared proof mechanism — a forcible map.  The correspondence stays a
genuine *narrative* (exp tame / log wild), carried by the essays; the
single-schema task is **not tractable** without first formalising "CF growth
rate" as an object, which is its own open problem.

## 4. The substrate's shape: metric facet vs topological facet — distinction pinned

This branch's `Shape213` / `GridReadout213`: raising the substrate
dimension makes the readout vector-valued — but the honest internal readout
is the *shape* (an ordered factorization), and dimension = number of
factors; the metric dressings (area, perimeter) were the import to drop.

Main's discrete Perelman / Ricci core (`discrete_perelman_core.md`,
curvature stencils): the genuinely presentation-invariant version of "the
substrate has structure beyond a single count" is *topological* —
curvature, Euler characteristic, the Ricci flow programme.

**Two readings — but two *different* enrichments, not one mechanism**
(refined this session; the earlier "two readouts of the same thing" framing
over-claimed).  Both go beyond a bare `ℕ` count, but in orthogonal
directions:

- **Shape = a vector.**  `Shape213.shape_splits`: the area
  (`shapeProduct`) is *under-determined* — distinct shapes share an area
  (`[1,6] ≠ [2,3]`, both product `6`), so a second coordinate (the
  `dimension` axis, `refine_increases_dimension`) is needed.  The count is
  non-injective; the fix is *more coordinates*.
- **Curvature = a sign.**  `DiscreteRicci.forman_determined_by_degree_sum`:
  the Forman curvature `4 − du − dv` is **fully determined** by the
  degree-sum — *not* under-determined.  Its "beyond a count" is that it
  lives in `ℤ`: a **difference-Lens** reading (count + sign), not a longer
  count-vector.  (A "same degree-sum, different curvature" collision — the
  shape-style under-determination — is provably impossible.)

So shape enriches the count into a **vector** and curvature into a **signed
difference**: two distinct moves past `ℕ`, sharing only the *negative* claim
"a single `ℕ` count is not the terminal readout once the substrate has
structure".  They unify at the level of `Lens.refines` (both are the
count-Lens refined), not by a common positive mechanism — so a single
non-vacuous schema is **not** available, and forcing one (e.g. pairing the
shape collision with a degree-sum/curvature collision) would import a *false*
lemma.  The honest bridge is the corrected distinction above, now pinned to
Lean on both sides.

## 5. ↔ ORIGIN_RAW (genesis record): the tower is the synchronous foliation Lens

`seed/ORIGIN_RAW.md` rebuilds Raw from "difference" alone and, in §6–§8,
flags a **lockstep tension**: proceeding stage-by-stage ("now that stage 1
is over, let us all convert the lines into points!") bundles each layer into
one synchronized step, but the honest substrate is *asynchronous* — two
local event kinds, no global clock (Event 1 [differentiation: Line→Point],
Event 2 [contrast: Pair→Line]).

The slot tower is generated by `iter` (`add_eq_iter`, `mul_eq_iter`): each
rung is the previous operation repeated a **counted** number of times — which
presupposes exactly the global clock §6 distrusts.  So the whole `append→+→×→^`
tower is the **synchronous foliation-Lens reading** of Raw growth, and the
generating `ℕ` (count) *is* the clock.  Raw-floor content is the two events;
`+`·`×`·`^` are the clock iterating on itself (consistent with the branch's own
"`^` = where iteration becomes an *operation*").

Two sub-correspondences land cleanly:

- **The two events = the tower floor + the sync/async axis.**  append =
  sequential stitch (Event 2 contrast, order-kept, `append_not_comm_general`);
  count/`+` = Line→Point reify (Event 1, order-erased, `add_comm_from_append`);
  `×` = the grid all-pairs-at-once (§6 lockstep, order-erased by transpose,
  `mul_comm_from_grid`).  Shared invariant: **commutativity ⟺ simultaneity
  ⟺ order-forgetting** — the branch's atom-(in)distinguishability handle and
  ORIGIN_RAW's lockstep-vs-stitch handle are one handle.
- **The +/× turn = where Raw's primitive distinguishing re-surfaces.**  `+`
  forgets which unit (`append_comm`, units indistinguishable); `×` recovers
  it as prime axes (`vp_mul`, the exponent vector remembers which prime).  The
  tower locates the exact rung at which the genesis primitive (다름) returns to
  the readout.

### Open questions seeded here

(a) **Is there an asynchronous number tower?**  The slot tower is the
synchronous version (iter against the clock); ORIGIN_RAW's async two-event
system is closed in `theory/math/foundations/async_growth.md`.  Do `+`/`×`/`^`
have async analogues, or is "operation" *definitionally* clock-dependent —
i.e. **count-Lens = the clock**, with no async counterpart?  The latter would
be a sharp, testable claim.

Sharpened against the axiom corpus, three statements collapse to one point.
`seed/AXIOM/10_encoding_costs.md` §10.1 (row 1) charges the `ℕ`-induction
principle as the **order-of-construction cost** ("inductive types presuppose
ℕ; ℕ is a Lens result of Raw, so importing it priorly is a cost").
ORIGIN_RAW §6 names the same thing dynamically — the **lockstep clock**.  The
`^`-essay (`theory/essays/analysis/what_is_exponentiation.md`) locates `^` as
"where iteration becomes an *operation*".  Read together: **operation-ness
*is* the §10.1 cost** — to run an operation you must count (the clock), and
counting is `ℕ`-induction imported in advance.  So the number tower is the
**cost of `ℕ` unrolled into a ladder** — `count-Lens = the clock = §10.1
row 1`.  If this identification holds, (a) is answered negative: there is no
asynchronous number tower, because operation *is* synchrony.  The tower
keeps the same architectural status as the §4.3 uniqueness proofs (pure-`ℕ`,
Raw-not-imported, conducted *inside* a `ℕ`-Lens codomain — not before/outside
Raw).  Open: state the three-way identity as one Lean fact, or find the
async operation that refutes it.

(b) **`^`-wall ↔ ORIGIN_RAW §9 "level-2 ceiling": resonance or identity?**
Both are "regularity runs out at a rung": §9 (sequential natural-number strata
stop at level 2) and the `^`-wall (comm/assoc die at `^`, the log does not fold
back — `two_three_unique`, `fold_iff_collinear`).  The resonance is plain;
asserting the *same* ceiling would be stereotype-matching.  Whether the two
ceilings coincide is open.

---

Status after this session (each verdict reached by inspecting the actual
Lean on both sides, not from the armchair):

- **Bridge 2 — CLOSED.**  Single schema `OrderWrap.no_order_of_wrap` + two
  instances (ℤ, ℤ/p), 9 PURE.  A genuine shared *mechanism* (the orbit-walk
  obstruction).
- **Bridge 1 — partly advanced.**  Size half pinned on the power side
  (`pow_eq_pow_iff_vp_support`, finite support).  The single cross-domain
  schema stays open: the weld and power certificates are indexed by
  different resolution types (truncation level vs support prime), so the only
  literal shared abstraction is the near-trivial "∀ level, local check".
  Needs a mechanism, not a `{cert, iff}` structure.
- **Bridge 3 — narrative only (formally disjoint).**  No shared formal
  object: "CF growth rate" is not formalised as a quantity, and it has no
  link to exponent-vector collinearity.  A single schema is intractable
  without first making "CF growth rate" an object.
- **Bridge 4 — distinction pinned (no single schema, by design).**  The two
  sides enrich the count in *different* directions (shape → vector,
  curvature → sign); `DiscreteRicci.forman_determined_by_degree_sum` (PURE)
  proves curvature is sum-determined, refuting the tempting (false) "same
  count, different curvature" unifier.  They share only the negative claim,
  unified at `Lens.refines`.

§5 adds the ORIGIN_RAW relation and questions (a)/(b) (still open).  The net
lesson: of the four, only bridge 2 had a genuine shared mechanism; 1 and 4
yield partial/negative Lean facts, and 3 is narrative.  Forcing the rest into
single schemas would be the forcible-map failure mode (and bridge 4's naive
unifier carried a *false* lemma).  Recorded so the correspondence — and the
verdicts — are tracked, not lost to chat.
