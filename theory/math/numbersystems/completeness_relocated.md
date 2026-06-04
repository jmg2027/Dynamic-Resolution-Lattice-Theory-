# Completeness as a Relocated Operation — the algebraic/transcendental split

The standard construction of the real numbers makes **completeness
constitutive**: ℝ is *defined* as the completion of ℚ (Cauchy sequences
modulo null sequences, or the set of all Dedekind cuts), and then
characterised up to isomorphism as "the complete ordered field".
Completeness is the defining axiom — it is what is added to ℚ to get ℝ.

A consequence usually passed over in silence: `√2` and `e` enter on
*identical* terms.  Both are simply elements of a complete field.  The
construction shows nothing about how their constructive costs differ — an
algebraic number you can pin with a finite decision rule and a
transcendental you cannot are, definitionally, the same kind of thing.

This chapter records a different arrangement, realised in
`lean/E213/Lib/Math/NumberSystems/Real213/`, in which **completeness is not in the
definition of a real at all**.  It re-enters only as one operation on
*sequences* of reals, and there it splits the reals sharply by where the
constructive cost actually lives.  Every claim below is a Lean fact,
∅-axiom (`#print axioms` clean), hence falsifiable per
`seed/AXIOM/08_falsifiability.md`.  Lean is the source of truth; this is
its mirror.

## 1. What a real is: a decision procedure, not a point

A Real213 value is a `ValidCut` (`Real213/Core/ValidCut.lean`): a
function

    c : ℕ → ℕ → Bool,    c m k  =  ⟦ x ≤ m/k ⟧

answering, at each rational probe `m/k`, whether the magnitude lies at or
below it — subject to two monotonicities (`upM` raising the numerator
preserves `true`; `dnK` lowering precision preserves `true` downward).

There is no hidden point `x` that `c` approximates.  `c` *is* the object;
what the real **is** is exhausted by what it answers.  Asking "what is
the number behind the cut?" imports an exterior the construction does not
have (`seed/AXIOM/05_no_exterior.md`): the pointing is the comparison
behaviour, and the comparison behaviour is all there is to point at.

This is what *tangible / 손에 잡힌다* means here — and it is worth
separating from a wrong turn the project already discarded.  Tangibility
is **not finiteness**.  An earlier framing tried to make reals concrete
by positing a largest resolution `N_U`, a universe-constant ceiling on
precision; that was an external dialer with no operand and is catalogued
as a failure mode ("Universe-constant framing").  The tangibility that
survives is **queryability**: for *any* probe `m/k` the cut returns a
definite bit in finite work, with no appeal to a completed totality.  A
real is graspable because you can interrogate it to arbitrary
precision — not because the precisions stop.

## 2. Completeness is a leaf of the import graph, not a root

That completeness is not constitutive here is a checkable fact about the
dependency graph, not a manner of speaking:

  - **The cut object needs no completeness.**  `Core/ValidCut`,
    `Sum/CutSum`, `Mul/CutMul`, `Core/CutPoset` — the type, arithmetic,
    and order — import nothing from `Analysis/CauchyComplete`.
  - **A named irrational needs no completeness.**  `PhiAsCut.phiCut`
    gives φ as a *closed-form decidable cut*,
    `phiCut m k := decide (k ≤ 2m ∧ 5k² ≤ (2m−k)²)`, with no Cauchy
    machinery anywhere beneath it.  φ is irrational and is written down
    directly as a comparison procedure, not obtained as a limit.
  - **Everything importing `CauchyComplete*` is downstream analysis** —
    bisection, Riemann integration, the `AbCutSeq` completion.  Nothing
    in the *definition* of a real, an *operation* on reals, or an
    *algebraic* real passes through it.

So completeness, in 213, is not what reals are.  It is one operation you
may perform on a sequence of cuts — take its limit — and its content is
the subject of the rest of this chapter.

## 3. The relocation: where completeness is actually load-bearing

Completeness is not eliminated.  It is moved to the one place genuine
non-constructivity lives, and made **visible as a hypothesis** instead of
hidden in a definition.  Three Lean files make the trichotomy exact.

### 3.1 The shared carrier — `AbCutSeq`

`Real213/AbCutSeq.lean`: **every monotone, positive-denominator sequence
of rationals is a Real213 cut.**  An `AbCutSeq` is a sequence `xs : ℕ →
Raw` that climbs (`IsAbMonotonic`) with positive denominators
(`IsAbPositiveB`).  From those two facts alone:

  - `cut n` (layer `n` as a Cut) is a `ValidCut` and `RatioCut`;
  - `cut_false_fwd` — a `false` reading **nests** forward (once the
    climbing rationals pass `m/k`, they stay past it);
  - `cut_eventually_const` — at any threshold with a `false`-witness the
    sequence is eventually constant (the per-`(m,k)` order-Cauchy fact);
  - `toCauchy` / `toCauchy_limit_valid` — *given a modulus*, the
    completed limit is again a `ValidCut`;
  - `limit_brackets` — the completed limit inherits any rational bracket
    its approximants establish.

This is more than any single constant: the cut representation is closed
under the limit operation for the whole class of climbing rational
sequences.  φ, e, π are then three instances of one structure.

### 3.2 Algebraic — completion is unconditional and redundant

`Real213/PhiAbCut.lean` makes φ an `AbCutSeq` (the even-indexed Fibonacci
convergents `fib(2n+2)/fib(2n+1)`; the monotonicity step **is** the
Cassini norm, `fib(2n+2)·fib(2n+3) + 1 = fib(2n+4)·fib(2n+1)` —
`cassini_mono_step`).  Because φ is algebraic, its order-Cauchy modulus
is **closed-form**:

  - `phi_cut_eventually_const` supplies `N(m,k) = 2k` with **no
    hypothesis** — past `2k` the convergent cut equals `phiCut m k`
    exactly (`FibCassiniNat.cs_eq_phiCut`);
  - `phiCompletion : CauchyCutSeq` is therefore a **closed term**;
  - `phiCompletion_limit_eq_phiCut` — completing the sequence recovers the
    closed-form `phiCut` on the nose.

For an algebraic real, completion is available unconditionally *and adds
nothing*: the limit was already writable as a finite decision procedure.
This is √2, the golden ratio, and their kin.

### 3.3 Transcendental — the modulus comes from the convergence rate

`Real213/ExpLog/EulerCut.lean` (e = Σ 1/k!) and `PiCut.lean` (π/2 via
Wallis, π by doubling) are the *same* `AbCutSeq` carrier.  Each constant
is genuinely located:

  - e is pinned strictly inside `(8/3, 3)` at every tail layer
    (`eulerCut_in_8_3_to_3`);
  - π/2 inside `(7/5, 2)`, π inside `(14/5, 4)` (`piCut_in_14_5_to_4`).

For **e** the completion is unconditional: e's convergents `a_i/i!` carry
a factorial tail rate, which yields a *total* ∅-axiom modulus
`N(m,k) = k+2` — `eulerCut` is constant past `k+2` at every threshold
(`ExpLog/EulerModulus.euler_total_modulus`, `euler_cut_const`), and e
completes as a `HolonomicReal` (`eHolonomicReal`) with the modulus a
constructed field.  The case-split on "`true` at every `n`" vs "`false`
at some `n`" is decided here by reading `eulerCut (k+1) m k`, because the
denominator gap `≥ 1/(k·(k+1)!)` exceeds the tail `< 1/((k+1)·(k+1)!)`.

The `LEM` refusal of `Cauchy/MonotonicBounded` (§180–194) bites only on a
**rate-free** presentation — the general monotone-bounded closure with no
stated rate.  `π` (`halfPiCut`) is in that posture *pending* its explicit
Wallis rate, so for now it completes via `AbCutSeq.toCauchy` with the
modulus supplied as a hypothesis; the obstruction is the missing rate,
not transcendence.

### 3.4 The trichotomy, stated

Same carrier, `AbCutSeq`; the difference is the modulus that completes it
— and the real line is **rate-carrying vs rate-free**, not
algebraic-vs-transcendental:

| Real                  | Cut object     | Completion modulus                       |
|-----------------------|----------------|------------------------------------------|
| rational              | `constCut a b` | trivial (constant sequence)              |
| algebraic (φ, √2)     | `AbCutSeq`     | **closed-form** `N=2k`, unconditional    |
| holonomic transc. (e) | `AbCutSeq`     | **closed-form** `N=k+2`, unconditional   |
| rate-free (π for now) | `AbCutSeq`     | **hypothesis** (no LEM-free total yet)   |

The classical construction collapses this table to one row: every real is
an element of a complete field, and the source of the modulus is
invisible.  Real213 keeps the column.  **A closed-form completion modulus,
here, just is the convergence rate made explicit** — present for the
algebraic reals (φ, √2) and for the holonomic transcendentals whose
recurrence supplies a rate (e), a fact the structure of the cut exhibits
rather than a property proved after the fact about points in a pre-built
continuum.

## 4. Why this is the rigorous form, and how it is falsifiable

The thesis is not "completeness is false" or "classical reals are wrong".
It is constructive and positive:

  1. a real is a decision procedure against the rationals;
  2. that procedure is the object (no exterior point);
  3. arithmetic, order, and the algebraic reals are built without ever
     invoking completeness;
  4. completeness re-enters only as a limit operation on sequences —
     unconditional for every rate-carrying real (algebraic φ/√2 and
     holonomic e), modulus-gated only for a rate-free presentation
     (π, pending its Wallis rate).

Each clause is a Lean fact, ∅-axiom:

  - (A) algebraic real with no completion — `PhiAsCut.phiCut` PURE;
  - (B) arithmetic/order independent of completion — the import graph;
  - (C) completion derived and, for algebraic reals, redundant —
    `PhiAbCut.phiCompletion_limit_eq_phiCut` PURE;
  - (D) completion unconditional for the holonomic transcendental e —
    `ExpLog/EulerModulus.euler_total_modulus` gives the total modulus
    `N=k+2` PURE (`eHolonomicReal`); only the rate-free closure
    (`Cauchy/MonotonicBounded` §180–194) is LEM-gated, and `PiCut` sits
    there pending π's explicit rate.

Falsification would be concrete: exhibit a Real213 arithmetic or order
theorem whose `#print axioms` reveals a dependence on `CauchyComplete`,
or a PURE *rate-free* total order-Cauchy modulus (one not derived from a
convergence rate — which would mean the §180 LEM barrier was illusory).
e's total modulus is *not* such a witness: it is built from the factorial
rate, exactly the data the rate-free closure lacks.

## 5. Grouping the groupings: the tower closes (no regress)

Completion groups an infinite family of threshold decisions into one cut.
A natural worry pushes the other way: if a real *is* the grouping of
infinitely many thresholds, then is the grouping itself just one more
threshold to be grouped — a sequence of groupings, then a grouping of
*those*, without end?  Does the construction only ever defer, never land?

`lean/E213/Lib/Math/Analysis/CompletionTower.lean` shows it lands, by
`rfl`.  The grouping operation is a **fixed point**, not a regress, for
three reasons that are each a one-line Lean fact.

  - **Type closure.**  `limit : CauchyCutSeq → (ℕ → ℕ → Bool)`.  A cut is
    `ℕ → ℕ → Bool`; a cut-*sequence* is `ℕ → ℕ → ℕ → Bool`.  Completion
    consumes the sequence and returns a cut — *the same type a single
    threshold-family already inhabits*.  The tower never escalates to
    ever-higher types; every level lands back on `ℕ → ℕ → Bool`
    (`tower_stays_in_cut`).
  - **Collapse.**  A level-2 tower — an outer cut-sequence whose `i`-th
    term is itself a completed limit — completes to *one* inner
    completion read at the outer modulus (`tower_is_single_inner`, `rfl`).
    No second object is built; the two levels flatten.  Completing a cut
    that is already a limit is the identity (`completion_idempotent`).
  - **Only the modulus moves.**  What accumulates up the tower is not
    objects but the **modulus** — level 2 reads at the composite of the
    inner and outer moduli.  And `tower_value_stable` makes the consequence
    sharp: once one completion pins the value at a probe, further grouping
    only re-indexes *which* layer answers — never the answer.

`Analysis/ModulusMonoid.lean` names the bookkeeping exactly.  The moduli
form a commutative monoid — pointwise `(ℕ, +, 0)`:

    Modulus := ℕ → ℕ → ℕ,   madd N₁ N₂ := (m,k) ↦ N₁ m k + N₂ m k,
    mzero := (m,k) ↦ 0,

with the laws `madd_zero_{l,r}`, `madd_assoc`, `madd_comm` (pointwise, so
∅-axiom), and the tower is an **action** of it: `tower_resolves_at_madd`
— the level-2 tower resolves at the composite `madd No Ni`, stacking
levels *adds* moduli; `identity_level_is_mzero` — the trivial grouping
adds the identity `mzero`.

This is the *same* `(ℕ, +)` bookkeeping as the `(ℕ,+)`-graded cut
transformers of `Analysis/ResolutionShift`, carried pointwise.  The link
is honest — a scalar grade `E : ℕ` is not literally a modulus function,
but it **embeds**: `gradeToModulus E := (m,k) ↦ E` is a *monoid
homomorphism* (`gradeToModulus_zero`, `gradeToModulus_add`), so the
ResolutionShift grade monoid sits inside the tower's modulus monoid as
the constant sub-monoid, and grade addition `E₂ + E₁`
(`IsResolutionShift_compose`) is `madd` of the embedded moduli
(`shift_grade_embeds`).  Grouping-of-groupings and resolution-shifting
are one `(ℕ,+)` — one scalar, one pointwise.

So the "threshold of thresholds of thresholds …" sequence is the
**self-similar floor** (`Theory/Raw/Lambek.self_similar_floor`) read at
the cut scale, under the scale-invariance of
`ObjectIsReadingScaleInvariant`: one fixed shape — *group an indexed
family into one object of the same kind* — recurring at every level, the
descent of moduli the only thing in motion.  This is the same structural
signature as the residue itself (peel and you find the same shape, the
descent terminates), now at the level of real numbers.  Tangibility
survives the iteration precisely because each grouping returns an object
you can query, of the kind you started with — the tower is a finite-depth
read at every probe, never an appeal to a completed infinity of levels.

## 6. The grade is a measurable amount of resolution — on the dyadic slice

Up to here the grade has been an abstract tag in `(ℕ, +)`: it composes
additively, embeds, stacks — but additively *over what*?
`Analysis/ResolutionQuantitative.lean` gives the tag its number, **in the
dyadic world**.

A `dyadicCut M E` is `constCut M (2^E)` — the dyadic rational `M / 2^E`.
The grade-`n` shifter `cutHalfIter n` sends it to `dyadicCut M (E+n) =
constCut M (2^(E+n))`: denominator `2^E ↦ 2^(E+n)`, value `M/2^E ↦
(M/2^E)/2ⁿ`.  So:

  - `grade_scales_denominator` — **grade `n` is exactly "`2ⁿ` finer"** on
    a dyadic cut: it multiplies the denominator by `2ⁿ`.
  - `grade_add_multiplies` — composing grades `a, b` multiplies the
    resolutions: `2^(a+b) = 2^a · 2^b`.  The additive grade monoid
    `(ℕ, +)` maps onto the multiplicative **resolution monoid (powers of
    2, ×)**.
  - `resolution_is_measurable` — a transformer carries *at most one* grade
    (grade uniqueness), so the amount is a well-defined number, read at
    one probe.

This is the quantitative form of the thesis *on the dyadic slice*.  But
it would overclaim to read "`2ⁿ` resolves every real" off it — and §7 is
the correction.

## 7. The resolving modulus is per-real; `2ⁿ` grades are the thinnest class

The grade picture of §6 is *constant in the probe*: a dyadic cut, the
same dyadic resolution `2ⁿ` everywhere.  But the probe space of a cut is
**every rational `m/k`**, not just dyadics, and the modulus that resolves
a real at probe `(m,k)` is in general a *function of the probe* — an
element of the full space `ℕ → ℕ → ℕ`, of which the constant grades are a
razor-thin slice.  `Analysis/ModulusForm.lean` makes this exact.

Each real carries its **own** modulus form, set by how fast its rational
approximants converge:

  - **dyadic** `M/2^E` — constant grade (the `ResolutionShift` slice of
    §6);
  - **φ** (algebraic) — its convergents are the Fibonacci pairs (`~ φⁿ`),
    and its resolving modulus is `phiModulus(m,k) = 2·k`
    (`PhiAbCut.phiCompletion`): **linear in the probe denominator**, not
    constant, not `2ⁿ`;
  - **e** (transcendental) — convergent denominators `n!`
    (`Cauchy/Euler.eulerDen`), a faster growth, hence a different
    per-threshold form again.

The separation is proved, not asserted: `phi_modulus_exceeds_every_grade`
— for *any* constant grade `E`, there is a probe (`k = E+1`) where φ's
modulus `2k` strictly exceeds it.  So no amount of uniform dyadic
resolution captures φ; `phiModulus_not_constant` and `grade_class_is_proper`
package this as: φ's resolving modulus is a genuine resolving modulus
(`phiModulus_resolves`) lying *outside* the constant-grade image — the
grade monoid of `ModulusMonoid` is a **proper** sub-structure.

So the honest quantitative picture is two-tiered.  Completeness relocated
to a graded action is, on dyadics, literally "sharpen by `2ⁿ`, composably"
— but the general real's modulus is a **richer probe-dependent form**, and
*the form itself is an invariant of the real*: φ's linear `2k`, e's
factorial-paced rate, a dyadic's constant grade are three distinct
signatures.  The modulus is not one universal ruler (`2ⁿ`); it is a
per-real law saying how much resolution each probe demands — which is what
"each real has its own modulus form, the grades being only the simplest"
means, now a theorem.

## Anchors

  - [`analysis/holonomic_modulus.md`](../analysis/holonomic_modulus.md) — the modulus
    as a constructed convergence rate: the general generator
    (`RateModulus.rate_total_modulus`) and the `HolonomicReal` instances (φ, e); the
    rate-carrying/rate-free divide made into a theorem
  - `lean/E213/Lib/Math/NumberSystems/Real213/RateModulus.lean` — `rate_total_modulus` (the general
    generator), `HolonomicReal.lean` — the bundled type, `ExpLog/EulerModulus.lean` —
    e's total modulus `N=k+2` + `eHolonomicReal`
  - `lean/E213/Lib/Math/NumberSystems/Real213/AbCutSeq.lean` — the shared carrier
  - `lean/E213/Lib/Math/NumberSystems/Real213/PhiAbCut.lean` — algebraic case
  - `lean/E213/Lib/Math/NumberSystems/Real213/ExpLog/{EulerCut,PiCut}.lean` —
    transcendental case
  - `lean/E213/Lib/Math/NumberSystems/Real213/PhiAsCut.lean` — φ closed-form cut
  - `lean/E213/Lib/Math/Analysis/CauchyComplete{,Valid}.lean` — the
    completeness operation and its closure under valid cuts
  - `lean/E213/Lib/Math/Analysis/CompletionTower.lean` — grouping the
    groupings closes (type closure, collapse, modulus composition)
  - `lean/E213/Lib/Math/Analysis/ModulusMonoid.lean` — the modulus monoid
    `(ℕ→ℕ→ℕ, +, 0)`, the tower as its action, ResolutionShift grades
    embedded as the constant sub-monoid
  - `lean/E213/Lib/Math/Analysis/ResolutionQuantitative.lean` — grade `n`
    = `2ⁿ`-finer resolution (dyadic slice); additive grade ↔ multiplicative
    `2^(a+b) = 2^a·2^b`; resolution measurable and unique
  - `lean/E213/Lib/Math/Analysis/ModulusForm.lean` — the resolving modulus
    is per-real (φ's `2k` ≠ any constant grade); the grade monoid is a
    proper sub-structure (`grade_class_is_proper`)
  - `lean/E213/Lib/Math/Analysis/ResolutionShift.lean` — the `(ℕ,+)`-graded
    monoid the tower's moduli compose in
  - `lean/E213/Theory/Raw/Lambek.lean` — `self_similar_floor` (the same
    shape at the Raw scale)
  - `lean/E213/Lib/Math/Analysis/Cauchy/MonotonicBounded.lean` §180–194 — the
    deliberate LEM refusal

Companions: `theory/math/real213.md` (the Real213 sub-tree),
`theory/math/phi_self_similarity.md §3.5` (φ as a Cauchy-complete limit
object).
