# The number tower — a general theory (slot tower → valuation tower)

A consolidation, stated as **general rules** rather than the discovery path.
It organizes the hyperoperation tower `append → + → × → ^ → ↑↑ → …` and its
number-theoretic content into one structure: *one generator (`iter`) read
through a tower of logarithms/valuations, over a slot ontology, with the
substrate-lattice dimension as the changing invariant and holonomy as the gauge
of the demotion above `^`*.

**Reading guide — every claim is tagged.**
`[∅]` = ∅-axiom Lean in this repo (file cited).  `[ax]` = a 213 axiom
(`seed/AXIOM/…`).  `[std]` = standard mathematics (true, not built here).
`[spec]` = suggestive, fenced (not asserted).  The discovery dialogue is in
`general_theory_metaanalysis.md` findings D/E/F/G/G′; this note is the cleaned
statement.

---

## R0 — Foundation: the tuple *is* the number (slot ontology)

`[ax]` (`slot_arithmetic.md` §1).  A number is a nested ℕ-tuple; **the tuple is
the number**, the nesting is the axis structure.  "ℤ / ℚ / ℝ" are **not kinds of
number** — they are names for the *operation-history of the axes*, realized as
**flattening Lens readouts**: `ℤ` is the difference-Lens on a count-pair
`(m,n) ↦ m−n` (itself *non-faithful*: `(1,3),(2,4) ↦ −2`).  Corollary
(witness-form discipline): describe with **lists / ℕ⁺**, never `a−c`/quotients —
leaving no seam for `0`, `−`, partiality, or `propext`.

The tower is therefore **list-native** `[∅]`:
`+` = unit-list **append** (`UnitList.count_append`), `×` = factor-list
**append** (`Shape213.shapeProduct_append`), `^` = factor-list **repeat**
(`Shape213.shapeProduct_lrepeat`).

## R1 — One generator: the tower is `iter` against the count-clock

`[∅]` (`HyperLadder`).  Every rung is the previous one iterated a *counted*
number of times: `hyperop (k+1) a b = iter (hyperop k a) b (seed k a)`
(`hyperop_succ`), with `+ , × , ^ = hyperop 1/2/3`.  The single engine is `iter`;
the count `ℕ` is the clock.  ("operation-ness = iteration against the one
count-clock.")

## R2 — Two law-directions: vertical survives, horizontal dies at `^`

`[∅]` (`HyperLadder` §4–§5).  The tower's laws split by **direction**:

- **Vertical (recursion-structural)** — properties of the `iter` recursion
  itself, so they hold at *every* level, generic in `k`:
  `hyperop_climb` (`H_{n+1}(a,b+1)=H_n(a,H_{n+1}(a,b))` — the law the tower runs
  on), `hyperop_right_zero/right_one/seed_self/arg_two/base_one`.
- **Horizontal (algebraic)** — commutativity, associativity, distributivity —
  properties of the *specific* operation; they hold only on the window `{1,2}`
  (`+`, `×`) and **die at `^`** (`HyperAssoc.pow_not_comm/pow_not_assoc`).  Both
  edges of the window fail, for *different* reasons (`k=0` ignores an argument;
  `k=3` distinguishes base/exponent).

## R3 — The logarithm demotes each rung; `vp` is the arithmetic log

`[std]` `log(a·b)=log a+log b` (`× → +`), `log(a^b)=b·log a` (`^ → ×`): each
operation *is* the previous one read in a log-coordinate.
`[∅]` (`VpMul`) `vp` is the arithmetic realization: `vp_mul` (`× → +`), `vp_pow`
(`^ → scalar·`).  So the tower is **one operation (addition) seen at successive
log-depths**.

## R4 — The lattice is the log-coordinate; its **dimension** is the changing invariant

`[∅]` (`ExpVector`, `FoldCriterion`).  The demotion lands the operation on a
lattice, and the **dimension of that lattice** is what changes up the tower:

- `+` lives on the **1-axis** count `ℕ` (one generator: the unit).
- `×` lives on the **∞-axis** prime lattice `⊕_p ℕ` (one axis per prime).

The jump `1 → ∞` is **atom-(in)distinguishability = lattice dimension**: units
are indistinguishable → one generator → 1 axis; primes are *independent*
(`prime_pow_unique`: distinct primes give independent axes) → ∞ generators → ∞
axes.  Hence `+` and `×` are **not** one operation at two resolutions — they are
addition on lattices of **different dimension**.  (This is the load-bearing
reframe; it sharpens "commutativity = atom-indistinguishability" from a
commutativity fact to a *dimension* fact.)

`^` is the first **non-addition** (scalar `·`, `vp_pow`): the operation-type
staircase is *translation* `{+,×}` → *scaling* `{^}` → *iterated scaling*
`{↑↑}`.

## R5 — Algebraic structure: canonical through `^`, holonomic above

`[∅]`+`[std]` (`FoldCriterion`, finding D).  *Associativity* gates **algebraic**
inverse-completion (the Grothendieck pair-construction needs it): `append`
(non-comm but assoc) → free group; `+ → ℤ`, `× → ℚ`, all algebraic.  *At `^`*
associativity dies → the inverse must be a **limit (a cut) = analytic**.
Separately, *commutativity* governs **single-vs-split** inverse: `+`,`×` have one
inverse; the non-commutative `^` **splits** into the **root** (base-solve,
algebraic — a real-closure cut) and the **logarithm** (exponent-solve,
transcendental — a non-folding cut).  Concrete `[∅]` witness:
`FoldCriterion.pow_inverse_splits` (`x³=8` has `x=2∈ℕ`; `3ˣ=8` has no rational
answer).  The fold criterion `fold_iff_collinear` is the **log-inverse
solvability test** (rational `x` ⟺ exponent-vectors collinear).  Above `^`: **no
completion** — fractional tetration solves the Abel equation
`F(x+1)=a^{F(x)}`, a 1-parameter family with no canonical member `[std]`.  The
∅-axiom barrier is exactly **transcendence**.

## R6 — Holonomy = the gauge of the demotion (not an obstruction)

`[std]` (iteration theory).  The demotion **always holds**; what changes at `^`
is its *coordinate*:

- through `^`: the demotion coordinate is the **ordinary log** — *canonical*
  (unique) → **flat**, zero holonomy → only the *modulus/certificate* is
  presentation-dependent, the **value is invariant** `[∅]`
  (`PresentationDependence.rcut_rescale`).
- at `↑↑`: the demotion coordinate is the **super-log / Abel** `α`
  (`α(a^z)=α(z)+1`, so `α(a↑↑b)=α(1)+b` — iteration *becomes addition*).  It
  exists but is **non-unique up to a 1-periodic function** → **curved**, nonzero
  holonomy → the **value itself** is presentation-dependent.

So **holonomy = the gauge group of the demotion** (the 1-periodic functions),
*not* a failure of the pattern.  Geometric reading (exact GR analogy): the
demotion coordinate is a connection; flat through `^`, curved above; holonomy is
how curvature is detected.  Price at `↑↑`: the Abel coordinate is *non-elementary*
(Kneser) and *gauge-ambiguous*.

## R7 — Each level's gauge-invariant is its valuation

`[∅]`+`[ax]`+`[std]`.  The gauge-invariant — what survives the holonomy — is, at
each level, a **valuation**; and a valuation *is* R3's demotion plus R8's
`∞/0 → finite` taming (defining laws `v(ab)=v(a)+v(b)` = the log, and `v(0)=∞`):

| level | invariant (valuation) | construction | `∞/0 → finite` |
|---|---|---|---|
| `+` | the size `n` | counting | limit ∞ = the point `[ax §6.5]` |
| `×` | **`vp`** (`p`-adic) `[∅]` | `vp_mul` = log | `vp_eq_zero_of_gt` = ∞-axes → finite support |
| `^` | archimedean (`ln|·|`, a cut) | log/cut | ∞-precision → finite cut |
| `↑↑` | **growth RANK** `[std]` | iterated-log depth | ∞-growth → finite coord (`ω`) |

`↑↑`'s invariant is the **rank** (level in the fast-growing / Hardy hierarchy),
not the value: a 1-periodic gauge is a bounded height-reparametrization,
invisible to "which tower level."  (GR: value/coordinate wobble = gauge; the
valuation/rank = the curvature-scalar invariant.)  So the **invariant tower is a
valuation tower**: `size → vp → cut → growth-rank`.

## R8 — The `∞/0 → finite` principle (`0 ≡ ∞`, the construction of the next valuation)

`[ax]` (`06_lens_readings.md` §6.5 `point ≡ K_∞ ≡ ∞`; §6.9 `0 ≡ ∞` at residue
level).  **When an invariant reaches `∞` or `0`, do not stop — give it a finite
coordinate; the basis is that `0` and `∞` are one residue.**  This is exactly
the construction of R7's next valuation (a valuation's `v(0)=∞` is the `0 ≡ ∞`
identity; the *finite value* it assigns is the taming).  (Lean realization caveat:
the Nat-valued `vp 2 0 = 0` picks the **"0"-reading** of the `0 ≡ ∞` residue;
`vp(0)=∞` is the dual reading — §6.9, *one residue / two Lens-readings*, not a
Lean value.)

---

## The theory in one paragraph

The number tower is **one operation (addition / `iter`) read through a tower of
logarithms**.  Each logarithm *demotes* a rung to the previous (R3) and lands it
on a **log-coordinate lattice whose dimension is the changing invariant**
(`1 → ∞ → …`, R4), driven by atom-(in)distinguishability.  Its **laws split
vertical (survive, the recursion) / horizontal (die at `^`, the algebra)** (R2),
and its **algebraic completion is canonical through `^` and absent above**
(associativity gates it; `^` splits the inverse root/log; ↑↑ has only an Abel
germ, R5).  The demotion **always holds**, but its coordinate goes from canonical
(flat, ordinary log) to **gauge-dependent (holonomic, Abel super-log)** at `↑↑`;
**holonomy is the gauge of the demotion** (R6).  The **gauge-invariant at each
level is its valuation** — `size → vp → cut → growth-rank` (R7) — and a valuation
*is* the demotion plus the **`∞/0 → finite` move** founded on `0 ≡ ∞` (R8).  All
of it sits on the **slot ontology** (the tuple is the number; ℤ/ℚ/ℝ are
flattening readouts; R0) and respects the residue/Lens boundary
(`boundary_discipline.md`): the readouts are Lenses, the invariants are faithful
valuations, the holonomy is presentation-dependence — never the residue itself.

## Scope, what is closed, and what is not

- **∅-axiom-closed (this repo)**: R0 list-form (`count_append`,
  `shapeProduct_append/lrepeat`); R1 (`HyperLadder`); R2 (`HyperLadder` §4–§5);
  R3 arithmetic side (`vp_mul`, `vp_pow`); R4 (`ExpVector`, `prime_pow_unique`,
  `toVec_tetration`); R5 fold side (`fold_iff_collinear`, `pow_inverse_splits`);
  R7 `×`-row (`vp_*`, `vp_eq_zero_of_gt`); the value-invariance below `^`
  (`rcut_rescale`).  R8 / the `0 ≡ ∞` basis are **213 axioms** (§6.5/§6.9).
- **Standard mathematics (true, not built here)**: R3 analytic log; R5
  transcendence (Gelfond–Schneider/Baker) and Abel non-uniqueness; R6 the
  super-log / Kneser solution and the 1-periodic gauge; R7 the growth-rank /
  Hardy-field valuation and surreal levels.
- **Fenced speculation `[spec]`** (recorded, *not* asserted): the tower as a
  stack of *higher* holonomies (2-holonomy / gerbes); any identification of the
  tetration-curvature with the repo's *discrete* Forman–Ricci (a pinned
  *distinction*, no shared generator — bridge 4); "Ricci tensor" as the specific
  object (the defensible object is *holonomy/connection*).

## Lean anchor index

`HyperLadder.{hyperop_succ, hyperop_one/two/three, hyperop_climb,
hyperop_right_one, hyperop_arg_two, hyperop_base_one, hyperop_zero_not_comm}` ·
`Shape213.{shapeProduct_append, shapeProduct_lrepeat, dimension}` ·
`UnitList.count_append` · `VpMul.{vp_mul, vp_pow}` · `Valuation.vp` ·
`VpSeparation.vp_separation` · `FoldCriterion.{pow_eq_pow_iff_vp,
fold_iff_collinear, vp_eq_zero_of_gt, pow_inverse_splits}` ·
`ExpVector.{toVec_mul, toVec_pow, toVec_faithful, toVec_finite_support,
toVec_tetration}` · `Real213.PresentationDependence.rcut_rescale` ·
`HyperAssoc.{pow_not_comm, pow_not_assoc}`.

## Open problems (the genuine frontier above `^`)

1. A 213-native **growth-rank valuation** (R7 `↑↑`-row): a ∅-axiom object that
   assigns the fast-growing hierarchy a finite rank — the analogue of `vp` for
   the iteration level.  (Today: standard Hardy-field theory only.)
2. The **Abel/super-log as a holonomic modulus** (R6): does the repo's
   `holonomic_modulus` / `PresentationDependence` machinery extend from
   modulus-holonomy (≤ `^`) to value-holonomy (`↑↑`)?  Where exactly do they meet?
3. **R5 transcendence barrier**: 213 proves the *non-folding* half (log escapes
   ℚ); the transcendence proper is beyond ∅-axiom — is any of it 213-reachable
   via the cut/presentation machinery?
