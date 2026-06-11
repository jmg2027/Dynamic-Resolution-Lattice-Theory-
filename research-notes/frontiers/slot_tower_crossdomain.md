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

**The genuine narrative insight (kept).**  Comparing the two equalities at
the Lean level: `cutEq cx cy := ∀ m k, cx m k = cy m k`
(`Real213/Core/CutPoset`) *defines* real/cut equality as agreement of the
per-level readout — a cut **is** its readout function.  On the integer side
`vp_separation` is the *theorem* that the prime-exponent readout is faithful
(UFD).  So **equality-as-readout-agreement is a *definition* on the continuum
side and an *earned theorem* on the discrete side** — same shape, two
epistemic statuses.  That is the real content of the bridge.

**Still open — and the obvious Lean schema is a dead end (tried, rejected).**
The natural move — a `LeveledReadout` structure (`eq`, `readout : X→Idx→Val`,
`sound`, `faithful`) with `eq_iff_readout : eq x y ↔ ∀ i, readout x i =
readout y i`, instantiated by `cutEq` (definitional) and `vp_separation`
(theorem) — was written and **adversarially rejected as vacuous** (a
three-way debate, skeptic verdict, file deleted before commit).  Why it
fails: `eq_iff_readout` is a one-line *tautological* unpacking of the
`sound`/`faithful` fields (it does zero work); the structure has **no generic
consumer** that proves anything over all faithful readouts; exposing
`readout` as a function is cosmetic over the forbidden
`{ cert : Prop, iff : eq ↔ cert }`.  The two instances are *stapled*, not
unified — fitting one definition and one deep theorem under a generic record
does not explain *why* one is definitional and the other earned (that "why"
is narrative, already in `equality_is_a_certificate.md`).  **Lesson for the
next attempt**: a non-vacuous bridge must be a theorem that does *generic
work* over faithful readouts (bridge 2's `no_order_of_wrap` rules witnesses
out; this container rules nothing out) — do **not** re-write the
`LeveledReadout`/`{cert, iff}` structure.  The mechanism remains genuinely
unfound; the size-half (`pow_eq_pow_iff_vp_support`) is the only Lean gain.

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

## 5. ↔ ORIGIN_RAW (genesis record): the tower is the clocked foliation Lens — (a)/(b) resolved

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

### Questions seeded here (both now resolved by debate)

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
Raw).

**Verdict (three-agent debate — affirmative / adversary / formalist).**  The
formal core is now **pinned in Lean** and the "async tower" question
**answered**, with the philosophical identity left as gloss (not forced into a
theorem).

- **The tower is one recursion turning the count-clock.**
  `Meta/Nat/HyperLadder.hyperop` (8 PURE): `hyperop (k+1) a b =
  iter (hyperop k a) b (seed k a)`, with `hyperop 1/2/3 = +`/`×`/`^`
  (`hyperop_one/two/three`).  This is the genuine single Lean fact the open
  question asked for — *not* the vacuous conjunction `add_eq_iter ∧
  mul_eq_iter ∧ pow_eq_iter`, but one `Nat`-recursion (the level `k`) whose
  only body is one `Nat`-iteration (the count `b` through `iter`).  Both
  indices are the *same* count-Lens: "operation-ness = iteration against the
  one count-clock".  The formalist confirmed **no hyperoperation ladder
  existed** in the repo (a real gap, now filled), and flagged the **funext
  landmine**: matching the rung flavours by `funext`/`rw`-on-functions pulls
  `Quot.sound` (axiom-dirty); the file stays PURE only via the pointwise
  `iter_congr` (induction, no funext).

- **The philosophical three-way identity stays gloss, not theorem.**  "the
  `Nat`-clock = the §10.1 ℕ-induction cost = ORIGIN_RAW's lockstep clock" is a
  *reading* of the count slot, not a Lean-statable equation; stating it as a
  theorem would be the vacuous/forcible move.  The honest formal content is
  the ladder; the identity is its narrative.

- **No async number *operation* — refined, survives.**  The adversary's
  hardest strike: `Convolution213.conv` is a genuine commutative operation
  that is *not* `iter`-shaped — it uses `natSplits n` (all `(i,j)` with
  `i+j=n`) as a *decomposition constraint*, not a forward count.  This shows
  "uses `Nat`" ≠ "forward-counts".  But the correction is that `conv` is **not
  async**: `natSplits`' all-pairs-at-once is precisely §6's **lockstep
  simultaneity** (the grid, `mul_comm_from_grid`), a *second* clocked
  foliation, not a clock-free one.  So there are two clocked readings —
  *sequential* (forward `iter`: the tower) and *simultaneous* (all-at-once:
  convolution/grid) — matching ORIGIN_RAW's two events (Event 1 sequential
  differentiation / Event 2 simultaneous contrast) and the
  commutativity ⟺ simultaneity handle above.  The only **clock-free**
  generator is `fire` (`Theory/Raw/Async`), which is an *event*, not an
  *operation*.  Refined answer: **every number operation is clocked** (in one
  of the two foliations); only events are clock-free.  "operation-ness is
  synchrony" holds once "synchrony" is read as *clocked* (sequential or
  simultaneous), not as *forward-counting alone* — the original phrasing
  over-narrowed.

(b) **`^`-wall ↔ ORIGIN_RAW §9 "level-2 ceiling": RESONANCE, not identity**
(two-agent debate — proponent / skeptic; both converged).  Both are
"regularity runs out at a rung": §9 (sequential natural-number strata stop at
level 2; `depthLe2_past_complete`/`depth3_boundary`, `level3_diverges`) and
the `^`-wall (comm/assoc die at `^` = `hyperop 3`; `pow_not_comm`/
`pow_not_assoc`).  The proponent's best line — "the order-2 swap symmetry is
adequate through level 2, insufficient at level 3" — does *not* survive: the
two boundaries are pinned by **different objects, swaps, predicates, and
mechanisms**, so asserting the *same* ceiling is exactly the named
stereotype-matching failure mode.

- **Different objects.**  Raw "level" = *tree depth* (nesting of `Raw.slash`;
  census `2,3,5,12,68`).  Tower "level" = *operation arity* (`hyperop` index:
  succ/`+`/`×`/`^`).  Incommensurable indices; the shared "2/3" is two
  countings, not one.
- **Different swaps.**  `level3_diverges` uses the *global* `Raw.swap` (an
  involution on the Raw *type*, `a↔b` relabel).  `pow_not_comm` is
  *argument*-swap of a `Nat→Nat→Nat` function.  Involution-on-trees ≠
  symmetry-of-a-Nat-operation.
- **Different predicates.**  The Raw ceiling is pinned by *past-completeness*
  (subterm/causal closure: depth-≤2 terms carry their whole past, depth-3
  miss a partner) — an *order* property.  The `^`-wall is comm/assoc loss —
  an *algebraic* property.  No shared Lean statement unifies them.
- **Different mechanisms.**  Raw: "subterm closure fails at depth 3" (slash-DAG
  reachability).  Tower: "the exponent becomes an *operation*, not a length"
  (`what_is_exponentiation.md`, type-promotion).  Two independent causal
  stories landing near the same number.

**Verdict: resonance, not identity — no Lean deliverable, by design.**  The
only formalizable statements are the *vacuous conjunction* of the two existing
facts (`level3_diverges ∧ pow_not_comm`) — which asserts "both hold", not
"same phenomenon" — so no file is written.  What *is* honestly shared is a
**phenomenological shape**: a downward-closed zone where some regularity is
total, then a boundary at the third rung where it fails.  Same shape, two
mechanisms.  Upgrading to identity would need a genuine bridge theorem
("past-completeness failure ⟺ commutativity loss"), which does not exist and
would be forced.  Closed as resonance.

---

Status after this session (each verdict reached by inspecting the actual
Lean on both sides, not from the armchair):

- **Bridge 2 — CLOSED.**  Single schema `OrderWrap.no_order_of_wrap` + two
  instances (ℤ, ℤ/p), 9 PURE.  A genuine shared *mechanism* (the orbit-walk
  obstruction).
- **Bridge 1 — partly advanced; one dead end closed off.**  Size half pinned
  on the power side (`pow_eq_pow_iff_vp_support`, finite support).  Genuine
  narrative insight recorded: equality-as-readout-agreement is *definitional*
  for cuts (`cutEq`) and an *earned theorem* for integers (`vp_separation`).
  The obvious `LeveledReadout`/`{cert, iff}` Lean schema was tried and
  **adversarially rejected as vacuous** (tautological `eq_iff_readout`, no
  generic consumer) — file deleted pre-commit; do not re-attempt.  The
  mechanism stays genuinely open (must do generic work over faithful readouts,
  like bridge 2's obstruction does).
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

- **§5 (a) — RESOLVED** (three-agent debate).  The tower is one recursion
  turning the count-clock: `Meta/Nat/HyperLadder.hyperop` (8 PURE),
  `hyperop 1/2/3 = +`/`×`/`^`.  No async number *operation* — every operation
  is clocked (sequential `iter` or simultaneous grid/convolution); only events
  (`fire`) are clock-free.  The philosophical three-way identity stays gloss,
  not theorem.  Funext landmine avoided via `iter_congr`.
- **§5 (b) — RESOLVED as RESONANCE** (proponent/skeptic debate, converged).
  `^`-wall ↔ ORIGIN_RAW §9 level-2 ceiling is *not* identity: different
  objects (tree depth vs operation arity), swaps (`Raw.swap` vs argument-comm),
  predicates (past-completeness vs comm/assoc), and mechanisms.  Only the
  vacuous conjunction is Lean-statable, so no file — forcing a unifier would be
  the stereotype-matching failure mode.  Shared content is a phenomenological
  shape (regularity total below, breaks at the third rung), not a mechanism.

The net lesson: of the four bridges, only bridge 2 had a genuine shared
mechanism; 1 and 4 yield partial/negative Lean facts, 3 is narrative; §5(a)
yields a genuine single Lean object (the hyperoperation ladder).  Forcing the
others into single schemas would be the forcible-map failure mode (and bridge
4's naive unifier carried a *false* lemma).  Recorded so the correspondence —
and the verdicts — are tracked, not lost to chat.
