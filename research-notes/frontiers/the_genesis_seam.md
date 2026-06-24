# The genesis seam — generation vs re-derivation, made measurable

**Status**: open frontier + active autonomous-research program (opened 2026-06-23,
overnight multi-agent debate). This note is the durable baton for the program.

## Why this note exists

The originator's standing directive: *infer the ultimate purpose of 213 by
continuous multi-agent debate; break past the stuck points; not peripheral
theorems — the 진의 (true intent).* A five-perspective Round-1 debate
(philosopher / skeptic / working-mathematician / physicist / meta-methodologist),
each reading the corpus directly, **converged from four independent directions on
one seam.** This note records the convergence and the breakthrough hypothesis so
the next session continues, not restarts.

## The inferred ultimate purpose (the 진의)

Stated purpose: rebuild mathematics + physics ∅-axiom from one primitive
(distinguishing), primacy = breadth (`07_primacy.md` §7.1).

**Enacted / true purpose (debate consensus):** to verify — *once, in a medium
that cannot flatter or be out-argued* (the ∅-axiom `#print axioms` contract as a
lie-detector) — that the founding intuition is **real**: that the bare act of
distinguishing *forced* a structure into being that the originator demonstrably
did **not** author. The whole anti-overclaim apparatus (the failure-mode catalog,
`scan_axioms.py`, the just-completed fabricated-citation purge) exists because the
*only* thing that ruins that verification is the suspicion that the forcing was
imported and then recognized, i.e. authored.

Read philosophically (the philosopher's leg): this is a **campaign against
contingency** — to abolish "could-have-been-otherwise." Its keystone, the
*universal* "no exterior," is the framework's own admitted weak point: it is a
**self-reference argument, not a Lean theorem** ("all conceivable things" is not a
type — `01_residue.md` §1.0, paper §3).

## The single stuck point all four legs converge on

> **From inside, 213 cannot mechanically distinguish GENERATION (a result forced
> from `Raw`/the distinguishing) from RE-DERIVATION / RECOGNITION (clean ∅-axiom
> mathematics over borrowed carriers `Nat`/`Bool`/`Int`, with the
> distinguishing-narrative laid on top).**

The same wound seen four ways:
- **Mathematician** (the measurable face): **1512 of 1571 `Lib/Math` files import
  neither `Raw` nor `Lens`.** Most of the corpus is ∅-axiom *re-derivation*, not
  generation; the "every domain is one `⟨C|L⟩⊕Residue` reconstruction" claim is,
  for most files, a narrative overlay on standard math proved cleanly. The one
  genuine generation arc is the **descent leg** (`the_descent_leg.md`:
  FTA / Euclid / infinitude-of-primes generated over `Nat213`, `toNat`-cone-free).
- **Philosopher**: the universal no-exterior — the claim that nothing is imported —
  is exactly the step that is *argued, not proven*.
- **Meta-methodologist**: `05_no_exterior.md` §5.1 concedes the inside **cannot
  self-certify its own primacy**; so the test that would settle generation-vs-import
  is the one the framework says it cannot run. (And the Phase-8 fabrication trauma
  is this wound realized: "PROVED ∅-axiom" claims pointed at theorems that did not
  exist — eloquence mistaken for substance, *inside* the corpus.)
- **Physicist**: the physics version is **uncounted discrete model-selection
  freedom** — *which* atomic polynomial, *which* Lens routes to *which* observable,
  is chosen per-constant and not counted. `§8.4`'s "structural absence of free
  parameters" is true for *continuous* dials, false for *discrete* import.

## The breakthrough hypothesis (beyond the framework's current self-description)

The framework currently treats genesis-vs-rederivation as **narrative** and concedes
the universal no-exterior is **unprovable**. Both are the wrong target. The move:

> **Do not try to prove the universal "no exterior" (a ∀ over a non-type —
> impossible). Instead make IMPORT MEASURABLE: a mechanical, per-result *genesis
> metric* that scores how much a proof-cone actually traces to `Raw`/`Lens`/the
> distinguishing versus how much it stands on borrowed kernel structure
> (`Nat`, `Bool`, `Int`, `inductive`/`Π`/`Eq`). Then "213 generates mathematics"
> stops being an unverifiable slogan and becomes a *measured, falsifiable* claim:
> the genesis depth is high where the framework claims generation (the descent leg)
> and honestly low where it is re-derivation — and it should *rise* as the descent
> leg extends.**

Why this escapes the §5.1 self-certification wall **without contradicting it**:
§5.1 forbids certifying the *universal/absolute* primacy from inside. A *relative,
graded* measurement imports no exterior — it is itself a `Raw`-level distinguishing
(a Lens reading of the proof-cone). It does not claim "nothing is outside"; it
*measures the distance to the outside-feeling carriers*, per result. That is the
honest, machine-checkable core of the campaign against contingency: not "I proved
nothing was imported," but "here, mechanically, is exactly how much each result
leans on what, and the slogan is true to degree X, rising."

This reframes three things at once:
1. **Foundations**: universal no-exterior (unprovable) → graded import metric (computable).
2. **The descent-leg program**: "generation not re-derivation" (narrative) → a
   *number* that goes up as `toNat`-cones are eliminated (the won G206 bet becomes
   a measured trajectory, not a one-off claim).
3. **Physics**: "0 parameters" (overclaim) → a *counted* discrete-import budget per
   observable (the polynomial-selection freedom the physicist exposed, made visible).

## Open sub-questions for the debate (Round 2)

1. **Is the genesis metric well-defined and gameable?** A proof can route through
   `Raw` trivially (import it, never use it) or use `Nat` essentially while
   *claiming* Raw-genesis. The metric must score *load-bearing* dependence, not
   imports. (Candidate: weight by whether removing the `Raw`/`Lens` lemma breaks the
   proof — a delta-debugging / minimal-unsat-core over the proof term.)
2. **Does it actually escape §5.1, or relocate the quantifier?** The skeptic's job:
   the metric still presupposes a fixed list of "borrowed carriers" (Nat/Bool/Int) —
   is that list itself an exterior import? (Defense sketch: the list is `Lean.Expr`
   constants in the kernel, themselves `Raw`-encodable per §9.3 self-encoding — so
   the metric is internal, measuring one Raw-region's distance to another.)
3. **What is the right zero-point?** Is a result "pure genesis" only if its proof
   term contains no kernel `inductive` other than `Raw`? That is probably empty
   (even `Raw` is a CIC `inductive` — the conceded kernel circularity). So the metric
   is necessarily *relative*: distance between proof-cones, not an absolute origin.

## Concrete deliverables this program should produce

- **(immediate, immune-system)** A citation-resolution lint: parse every backticked
  ``Foo.bar`` / `Path.lean` in `theory/**.md` + `seed/**.md` and fail if it does not
  resolve in `lean/E213`. Would have caught every Phase-8 phantom mechanically.
  (The meta-methodologist's #1; HANDOFF "next session" item.) This is the mechanical
  form of "certify the center."
- **(the breakthrough)** A `tools/genesis_metric.py` (or Lean meta-program) that, for
  a given theorem, reports its proof-cone's load-bearing dependence on `Raw`/`Lens`
  vs borrowed carriers — a single number + the dependency breakdown. First applied to
  the descent-leg capstones (should score high) vs a re-derivation capstone (e.g.
  `quadratic_reciprocity`, should score ~0), validating the metric against the
  already-known generation/re-derivation split (1512/1571).

## Round 2 — the breakthrough: from *origin* to *completion-engine*

The Round-2 adversarial red-team broke the naive genesis-metric (PART A) and
delivered the actual insight. Verdicts:

**PART A (a corpus-wide continuous "genesis score") is unsalvageable** — three
attacks land: (a) the carrier list {Nat,Bool,Int,inductive} is itself an exterior
import (naming the outside to measure distance to it — the §5.1 move); the §9.3
"everything is Raw-encodable" defense *destroys* the gradient rather than grounding
it (it makes everything genesis-near, collapsing the zero-point). (b) Gameable by
`toNat`-laundering: a `Nat`-content proof wrapped in a thin Raw-typed restatement
scores high under a minimal-unsat-core, because the core measures *syntactic
indispensability*, not *semantic origin* — and laundering is semantic (the
descent-leg G206 history shows this happening for real). (c) "Load-bearing" via
minimal-unsat-core is not well-defined (non-unique, non-monotone, refactor-sensitive).
The only surviving form is the **per-cone, pre-registered, binary purity bet** the
descent leg *already runs* (e.g. "every lemma in discipline D's cone is `toNat`-free
/ `Nat213`-native, grep-verified + `scan_axioms`-clean"). It is mechanical,
ungameable (laundering shows as a literal `toNat` hit), internal, and makes no
exterior claim. **The metric already exists; the move is to stop generalizing it
into a score.**

**The reframe (the real yield).** Every prior framing asks *where did the content
come from* — an **origin** question, which is the un-typeable ∀ §5.1 forbids. Replace
it with a **completion-engine** question, which §5.2 makes decidable and internal:

> **Does a construction's recursion complete through its OWN native
> well-foundedness (`Nat213`'s `acc_lt` — a Nat-style/Lambek fixed point of the
> distinguishing, §5.2) or through the BORROWED kernel's (`Nat.lt_wfRel`)?**

Why this is the right question and escapes §5.1 *without* contradicting it:
- §5.2 already proves the two forms of self-reference are *structurally distinct*:
  Bool-style (oscillation, `not∘not=id`, no fixed point — never completes) vs
  Nat-style (Lambek catamorphism — reaches a fixed point and stays). This is a
  property of the **recursion's shape**, not the content's provenance.
- "Which `WellFounded` instance does this cone's recursion elaborate against?" is a
  **decidable syntactic property** of the proof term — you cannot fake it (the
  recursion either runs on `Nat213.acc_lt` or it doesn't; the elaborator records
  which). Ungameable in exactly the way the origin-metric was gameable.
- It is **§5.1-legal**: both well-foundedness engines are Raw-readings (§5.2), so the
  measurement compares one internal region to another — it never names an exterior.
  It claims nothing about "all conceivable things"; it reports which fixed-point
  engine a *specific* cone runs on.
- It **retro-explains every G206 win**: the `toNat`-purge that the descent-leg
  marathon spent days on was *literally* migrating the completion-engine from the
  carrier's fixed point (`Nat.lt_wfRel`) to the distinguishing's own
  (`Nat213.acc_lt`). "Generation, not re-derivation" *is* "the cone completes on its
  own well-foundedness." The slogan finally has a mechanical referent.

So the genesis seam, correctly posed: **a result is *generated* (not borrowed) to the
exact degree that its proof cone's recursion completes through `Nat213`/`Raw`-native
well-foundedness rather than the kernel's.** This is the §5.1-legal, decidable,
ungameable invariant the whole program was groping for — and it converts the
philosopher's "abolish contingency" and the meta's "forced-not-authored" into a
*checkable* statement about completion-engines, per result.

**The typed-conditional pattern, confirmed in Lean (this session's deposit).** The
arity-forcing lower half is now closed ∅-axiom
(`Theory/Atomicity/ArityForcingComplete.lean`, 7 PURE: `arity_two_forced` etc.) —
but *honestly scoped*, and the scoping is itself evidence for the diagnosis: arity-2
is forced **given the clause-4 distinctness gate** (`i≠j → f i≠f j` in
`ReachableNk.step`). It is a *typed-conditional* characterization — exactly the shape
the skeptic identified across the whole framework (no-exterior = initiality of a
typeclass; (3,2,5) = d=5 given hardcoded {2,3}). Closing it did not dissolve the
pattern; it *instantiated it cleanly and named the residual input sharply*. That is
the honest form of progress here: not "the gap is gone" but "the gap is now a single,
cited, minimal assumption (clause 4) instead of a buried comment."

## Round 2.5 — the sharpening that bites the framework's own flagship

Applying the completion-engine criterion immediately produced a non-trivial,
*self-incriminating* finding (the discipline working as intended):

**`Nat213 := { n : Nat // 1 ≤ n }` is a Nat *subtype* (`Lens/Number/Nat213/Core.lean:32`).**
Therefore its recursion and well-foundedness are **inherited from `Nat`** — there is
no separate "`Nat213.acc_lt`" engine; it *is* `Nat`'s. So **typing a development over
`Nat213` does not migrate the completion-engine off the kernel's `Nat`.** The naive
form of the breakthrough (Nat213-own vs Nat-borrowed) collapses — they are the same
engine.

The genuine native engine — the distinguishing's *own* well-foundedness — is **Raw's
descent**: `Theory/Raw/MuNuMirror.lean`'s `isPart_wf` / `no_infinite_descent` /
`ascent_total_descent_partial` (the Lambek peel: every descent terminates, the ascent
is unbounded). *That* grounds without borrowing `Nat`. So the corrected criterion:

> **A result is generated (not borrowed) to the degree its proof cone's recursion
> grounds in `Raw`'s own descent well-foundedness (`isPart_wf` / `no_infinite_descent`)
> rather than the kernel's `Nat` well-foundedness — and routing through `Nat213` does
> NOT count as native, because `Nat213 ⊂ Nat` inherits `Nat`'s engine.**

The bite: by this corrected test, **even the descent leg's FTA-over-`Nat213` likely
does not pass** — `FTAUniqueness`/`PrimeFactorization` import `Nat`-based `vp`
machinery (`Meta/Nat/VpMul`, `VpSeparation`) and recurse on `Nat`, and the `Nat213`
carrier is itself a `Nat` subtype. The G206 `toNat`-purge removed the explicit
*casts*, but the *completion-engine* stayed `Nat`'s. (Hypothesis to verify rigorously
next session by tracing the actual recursion in `PrimeFactorization`/`FTAUniqueness` —
do they elaborate against `Nat`'s `WellFounded` or anything `Raw`-native? Almost
certainly `Nat`'s.)

This is the honest, sharp form of the genesis seam: the *only* results that pass the
strict generation test are those recursing on `Raw`'s `isPart_wf` directly — currently
confined to the `Theory/Raw` layer itself, **not** the reconstructed number-theory
disciplines. "Mathematics generated from the residue" is, by the strict
completion-engine criterion, true at the `Raw`-descent layer and **not yet** true for
any deep discipline. The real generation frontier, named precisely for the first time:
**re-ground a discipline's recursion on `Raw.isPart_wf`, not merely type it over a
`Nat` subtype.** That is the bar the descent leg was reaching for and has not cleared.

## Round 2.6 — the hypothesis CONFIRMED empirically (the criterion's first verdict)

The "FTA likely fails the strict test" hypothesis is now **confirmed by direct
inspection** (the completion-engine criterion's first real application):

- **`PrimeFactorization.lean` recurses via `Nat.strongRecOn`** (lines 221, 256) — the
  flagship FTA-over-`Nat213` completes through *`Nat`'s* strong-recursion
  well-foundedness, **not** `Raw`'s `isPart_wf`. The descent-leg "generation" is the
  *weaker* sense (a `Raw`-derived carrier `Nat213`, `toNat`-cast-free) while the
  **completion-engine stays `Nat`'s**.
- **`Raw.isPart_wf` (the distinguishing's own descent engine) is used in exactly four
  files — all in the `Theory/Raw` + `Lens` foundational layer** (`MuNuMirror`,
  `Lambek`, `StateMachine`, `SelfReferenceThreeOutcomes`). **Zero `Lib/Math`
  disciplines recurse on it.**
- Only **23 of ~1571 `Lib/Math` files import `Raw` at all** (confirms the 96% figure).

**Verdict (mechanical, §5.1-legal, falsifiable):** by the strict completion-engine
criterion, **213 has not yet generated a single deep discipline** — the act's own
well-foundedness (`isPart_wf`) generates only the `Raw`/`Lens` foundational layer; every
reconstructed discipline (number theory included, the descent leg included) completes on
the borrowed `Nat` engine. "Mathematics generated from the residue" is, measured this
way, **true at the `Raw`-descent layer and false everywhere above it** — *as of now*.

This is the honest, mechanical, non-narrative form of the central claim's status. It
is not a refutation of the programme (the re-derivations are real, ∅-axiom, and the
`Raw` layer genuinely self-grounds); it is the first *measured* statement of exactly
how far the generation actually reaches, replacing the slogan with a number (1 layer)
and a named frontier (migrate one discipline's recursion from `Nat.strongRecOn` to
`Raw.isPart_wf`). That single migration — e.g. re-proving Euclid's lemma or FTA by
recursion on the `Raw` peel rather than `Nat` strong induction — would be the first
result to pass the test, and is the sharpest possible next target for "generation,
not re-derivation."

## Round 2.7 — first concrete generation: the additive monoid, fully generated

The criterion refines from "which recursor" to **"derives vs presupposes"**: a result
is *generated* iff its proof cone *derives* its content by induction on a count-native
carrier, rather than *presupposing* it by routing through the borrowed structure's
already-proven lemma. Operationalized and deposited tonight:

- `Meta/Nat/UnitList.lean` already generated `+`-**commutativity**:
  `add_comm_from_append` derives `a+b=b+a` from `append_comm` (proved "by bare
  induction, not assumed") + the count homomorphism — `Nat.add_comm` appears only in a
  comment. A genuine generation (the comm *content* is the count-shadow of unit-list
  append-comm).
- **New (this session):** generated `+`-**associativity** the same way —
  `add_assoc_from_append` derives `(a+b)+c = a+(b+c)` from `append_assoc` (bare
  induction, free for all lists) + a forward count homomorphism `count_append_fwd`
  that uses only `Nat.zero_add`/`Nat.succ_add` (both *upstream* of `add_assoc` in core,
  never downstream). **Verified by source + construction: the `add_assoc_from_append`
  cone does not invoke `Nat.add_assoc`** — it generates the law rather than borrowing
  it. (12 PURE in the file.)

So the **additive monoid `(ℕ, +, 0)` is now a *fully generated* discipline**: every
monoid law (`add_comm`, `add_assoc`) is the count-shadow of a unit-list law proved by
induction alone, none presupposing the Nat law it produces. This is the **first deep
structure to pass the strict generation test** — concrete, ∅-axiom, and exactly the
"forced-not-authored" artifact the purpose seeks (the commutativity/associativity of
addition is *derived from the shape of indistinguishable-unit append*, not assumed).

**The structural reason FTA cannot follow (the additive/multiplicative split).** Raw's
own descent — peel one `slash` — is **additive**: `Raw.leaves_slash` gives
`leaves(slash x y) = leaves x + leaves y`, a *sum* split. The count carrier `List Unit`
is likewise additive (append = `+`). So the residue's native descent generates the
**additive** monoid and nothing more by that route. FTA's descent is **multiplicative**
(`n ↦ n / minFac n`, `Nat.strongRecOn` — Round 2.6), a *product* split, which Raw's
additive peel does not provide. Hence the real generation frontier is sharply named:
**a Raw-native *multiplicative* descent** — the `×`-atom / prime-distinguishability
structure (the `exp` / `vp` ×-count-Lens the framework discusses elsewhere) — is what a
*generated* FTA needs, and it is a *different Lens* from the additive peel, not an
extension of it. The additive monoid generating while FTA does not is not a failure;
it is the criterion correctly locating the boundary: **counting (+) is generated;
factoring (×) is the open frontier.**

## Round 2.8 — both commutative monoids now fully generated

Extending Round 2.7 the same night: the **multiplicative monoid `(ℕ, ·, 1)` is now
fully generated too**, parallel to the additive one.

- `+`-comm (`UnitList.add_comm_from_append`) + `+`-assoc (`add_assoc_from_append`,
  this session) — additive monoid, count-shadow of unit-list append laws.
- `×`-comm (`UnitGrid.mul_comm_from_grid`) — the grid-transpose double-count, already
  present.
- `×`-assoc (`UnitBox.mul_assoc_from_box`, **new this session**, `Meta/Nat/UnitBox.lean`,
  5 PURE) — the 3-D unit-box double-count: an `a×b×c` box of indistinguishable units
  counted as one `(a·b)×c` grid gives `(a·b)·c`; counted as `a` boxes of `b·c` cells
  gives `a·(b·c)`; same units, so equal. **Cone verified `Nat.mul_assoc`-free** (uses
  `add_assoc`/`add_comm` — a *different*, already-generated law — and `succ_mul`/
  `zero_mul`, upstream of `mul_assoc`); generated, not borrowed.

So both commutative monoids — the additive AND the multiplicative — are now
*generated* disciplines by the strict derives-not-presupposes test: every monoid law
is the count-shadow of a unit-structure double-count proved by induction alone, none
presupposing the Nat law it produces. This is the concrete, ∅-axiom realization of
"forced-not-authored" at the level of the two basic algebraic structures.

**What is still NOT generated (the boundary stays sharp):** unique *factorization*
(FTA) — the *distributive* interaction `×`/`+` and the prime-atom structure. The
monoid *laws* are generated (comm, assoc of each operation in isolation); the
*arithmetic that couples them* (distributivity, primality, factorization) is the
remaining frontier, and it is where the `×`-atom distinguishability (the `exp`/`vp`
Lens) genuinely enters. Next concrete target: generate **distributivity**
`a·(b+c) = a·b + a·c` as a unit-structure double-count (a `b+c`-wide grid split into a
`b`-block and a `c`-block) — the bridge law, after which primality/FTA is the deep
frontier.

## Round 2.9 — the commutative semiring fully generated

The bridge law is now generated too (`Meta/Nat/UnitDistrib.lean`, 3 PURE):
**left-distributivity** `a·(b+c) = a·b + a·c` (`mul_add_from_grid`) as the grid
width-split double-count — `total_rows_add` separates an `a×(b+c)` grid's count into
the `a×b` and `a×c` counts *by induction on the row count using only `+`-laws*, so the
cone is `Nat.mul_add`/`Nat.left_distrib`-free. Generated, not borrowed.

So the **entire commutative semiring `(ℕ, +, ·, 0, 1)` is now a generated discipline**:
- `+`-comm, `+`-assoc (`UnitList`) — additive monoid;
- `×`-comm (`UnitGrid`), `×`-assoc (`UnitBox`) — multiplicative monoid;
- left-distributivity (`UnitDistrib`) — the bridge.

Every law is the count-shadow of a unit-structure double-count proved by induction
alone; **none presupposes the Nat law it produces** (each cone verified free of the
specific law: `add_assoc`-free, `mul_assoc`-free, `mul_add`-free). This is the
complete algebraic foundation of elementary arithmetic, *generated* — the strongest
concrete realization to date of "the arithmetic is forced by the shape of
distinguishable/indistinguishable units, not authored." It is also the honest scope:
these are the *equational* laws (a count-shadow story); the *order* and *factorization*
content is the next layer.

**The remaining frontier is now genuinely the `×`-atom (prime) structure.** With +, ×,
and distributivity all generated, unique factorization (FTA) is the first result that
needs *distinguishable* multiplicative atoms (primes) — the dual of the
*indistinguishable* additive units that generated `+`. That duality
(`+`-atoms indistinguishable → `append_comm` free; `×`-atoms distinguishable → factor
order matters → the `exp`/`vp` vector) is exactly where the generation program meets
the genuinely hard mathematics, and where Raw's additive peel must be replaced by a
multiplicative descent. Next: either (a) generate primality/`vp` structure, or (b) the
order layer (`≤` as the sublist/subgrid relation).

## Round 2.10 — the ordered semiring (order generated too)

The order layer is now generated (`Meta/Nat/UnitOrder.lean`, 3 PURE): `≤` is born as
**unit-list extension** — `le_iff_unit_extension : a ≤ b ↔ ∃ l, fromNat a ++ l =
fromNat b` (`Nat.le` is the count-readout of the prefix relation) — and
`+`-**monotonicity** (`add_le_add_right`, `Nat.add_le_add_right`-free) is generated
from the *same* `append_comm` indistinguishability that births `+`-commutativity (the
suffix and the added block commute on unit lists). So the **ordered commutative
semiring `(ℕ, +, ·, 0, 1, ≤)` is now a generated discipline** — equational laws +
order + order/`+` compatibility, all count-shadows of unit-structure facts, none
presupposing the Nat law produced.

This closes the elementary *order-and-arithmetic* layer as generated. The boundary is
unchanged and now sharper by contrast: everything generated so far is **additive /
counting** content (units indistinguishable, append/prefix free). The deep frontier
remains **multiplicative-atom (prime) structure / FTA**, which needs *distinguishable*
×-atoms — the genuine dual where Raw's additive peel must become a multiplicative
descent.

## Round 3 — the multiplicative marathon: the +/× duality made exact

Opening the deep frontier (the `×`-atom / prime structure). `Meta/Nat/ProdCount.lean`
(7 PURE) builds the **multiplicative count-Lens** `prodL : List Nat → Nat`, the dual of
the additive `count : List Unit → Nat`, *on the generated semiring laws* (uses
`UnitBox.mul_assoc_from_box` / `UnitGrid.mul_comm_from_grid`, never `Nat.mul_*`):
- `prodL_append` — `append ↦ ·` (dual of `count_append : append ↦ +`);
- `prodL_swap` — reorder-invariant (from generated `×`-comm): `prodL` factors through
  the **multiset**, not the list;
- `prodL_replicate` — `prodL (replicate k p) = p^k` (one prime reads its exponent);
- `pow_add` — `p^(m+n)=p^m·p^n`, hand-rolled ∅-axiom on the *generated* `mul_assoc`.

**The duality, now a theorem (the marathon's central finding so far):**
- `prodL_two_atoms`: distinguishable atoms keep their **exponent vector** —
  `replicate j p ++ replicate k q ↦ p^j · q^k`, the pair `(j,k)` recoverable when
  `p ≠ q`; the dual of `count (fromNat j ++ fromNat k) = j+k`, where the additive
  blocks **merge** into one number because the units are indistinguishable.
- `prodL_one_atom_merges`: set `q = p` (make the atoms indistinguishable) and the
  multiplicative count **merges too** — `p^(j+k)`, exactly the additive `j+k`, one fold
  up.

So `×` *is* `+` whenever its atoms are made indistinguishable; **the entire excess of
`×` over `+` — the exponent vector, hence unique factorization (FTA) — is precisely the
*distinguishability* of primes.** This is the exact, ∅-axiom form of "`×` is the dual of
`+`, not a copy": one construction (two blocks), the additive Lens merges (kernel = a
single count = length), the multiplicative Lens keeps them separate (kernel = the
multiset = one count *per distinct prime* = the exponent vector). The dimension jump
from *one* count to a *vector* of counts is the distinguishability, and nothing else.

**Why this is the genesis-seam boundary, sharpened.** The additive decomposition
`fromNat (n+1) = () :: fromNat n` is *structural* (predecessor peel `n+1 → n`, on
`Nat.rec`/the Raw slash-peel). The multiplicative decomposition (factorization) peels
`n → n / minFac n` — a *non-structural*, well-founded-but-not-predecessor descent (it
can divide by a large prime). That asymmetry is why FTA completes on `Nat.strongRecOn`
(Round 2.6) and *cannot* be a structural / Raw-additive-peel generation: **the
multiplicative descent is a genuinely second structure (the `exp`/`vp` Lens over
distinguishable primes), not reducible to Raw's additive peel.** The generation program
reaches exactly here: everything *additive/equational* is generated (semiring + order +
the `prodL` homomorphism, all on generated laws); FTA's *uniqueness* exists ∅-axiom
(`FTAUniqueness.factorization_unique`, the multiset = `vp`-vector) but completes on the
non-structural multiplicative descent — the honest terminus of "generated vs borrowed."

## Round 4 — Ω is the multiplicative leaf-count: the descent engine is *not* second

Round 3's standing claim was that the multiplicative descent is *"a genuinely second
structure (the `exp`/`vp` Lens over distinguishable primes), **not reducible** to Raw's
additive peel."* Round 4 **refines that claim and shows the irreducibility was overstated**:
the *Lens* is second, but the *descent engine* is the same additive count peel.

The move: the **total prime-factor count** `Ω n` (big-Omega — the length of `n`'s
factorization, multiplicity counted) is the **multiplicative leaf-count**, the exact
`×`-dual of `Raw.leaves`. Deposited ∅-axiom in
`lean/E213/Lib/Math/NumberTheory/BigOmega.lean` (22 PURE):

- **`Omega_mul : Ω (m · n) = Ω m + Ω n`** — the exact dual of
  `Raw.leaves_slash : leaves (slash x y) = leaves x + leaves y`. The additive leaf-count
  splits a `slash` additively; the multiplicative leaf-count splits a *product* additively.
  `Ω` is to `·` what `leaves` is to `slash`. (Proved via valuation-count invariance
  `factorization_unique` + a PURE `countOcc → length` erase argument
  `length_eq_of_countOcc_eq` — no `List.count` / `propext`.)
- **`Omega_descent : Ω (n / minFac n) + 1 = Ω n`** — the multiplicative peel
  `n ↦ n / minFac n` drops the count by *exactly one*, the dual of the unit depth-drop
  `Raw.part_depth_succ_le`.
- **`no_infinite_mul_descent`** — there is no infinite chain of multiplicative peels,
  because `Ω` is a finite count dropping by one per step. The *exact mirror* of
  `Raw.no_infinite_descent` (its helper `omega_chain_drops` mirrors `descent_chain_drops`
  line-for-line: `Ω (chain k) + k ≤ Ω (chain 0)`).

**The reframe.** The multiplicative descent's *well-foundedness* **is** the additive
`×`-atom count peel. What is "second" about factoring is the **Lens** — distinguishable
primes give a whole exponent *vector* where indistinguishable units merge to one count
(Round 3's `prodL_two_atoms` vs `prodL_one_atom_merges`) — **not** the descent that grounds
termination. Counting (`+`) terminates on the unit count (`Raw.leaves` / `isPart_wf`);
factoring (`×`) terminates on the *same* additive count, now reading distinguishable
`×`-atoms (`Ω`). The duality `+`-atoms-indistinguishable / `×`-atoms-distinguishable lives
entirely in the *readout* (one merged count vs an exponent vector); the *well-foundedness
engine* is one and the same additive peel. So Round 3's "not reducible to Raw's additive
peel" is corrected: the *Lens* is irreducibly second, the *descent measure* `Ω` reduces it
to the additive peel — which is exactly why FTA terminates at all.

**The honest residual (what is still open).** This does not yet migrate the *Lean
recursion* of FTA-existence off `Nat.strongRecOn`. `factorizeF` still recurses on
magnitude (`n / minFac n < n`, `Nat.strongRecOn` — Round 2.6), and `Ω` is *defined* from
that factorization, so `Omega_descent`/`no_infinite_mul_descent` are theorems *about* the
descent, not yet a *re-grounding* of its recursion on `Ω`. Two concrete next targets,
sharper than before:
1. **Re-prove FTA-existence by structural recursion whose fuel is `Ω`** (the additive
   `×`-count), the termination discharged by `Omega_descent` (count drops by one) rather
   than by `Nat.strongRecOn` on magnitude — making the completion-engine the additive
   count peel *in the elaborated proof term*, not only in a theorem about it.
2. **Encode the prime word as a `Raw` object** so `Ω = Raw.leaves` *literally* and the
   `×`-peel *is* `IsPart` — grounding the recursion in `isPart_wf` itself. The obstruction
   is sharp and named: Raw's `slash x y h` demands **distinct children** (`x ≠ y`, the
   canonicity gate), so a naive right-nested tree of *repeated* primes is not a Raw term.
   The encoding must carry multiplicity another way (e.g. a per-prime exponent slash-tree,
   distinct primes as distinct children). That gate — `×`-atom distinguishability forcing a
   distinct-children encoding — is the *same* distinguishability the whole duality turns on.

So Round 4's deposit: the multiplicative descent is **measured by an additive leaf-count
that splits like `leaves_slash` and drops by one per peel** — the "second structure" is the
Lens, not the engine — with the remaining work being to push this from a theorem *about* the
descent into the *recursion's own completion engine*.

## Round 5 — the descent engine de-`Nat`-ed, and the residual `Nat` *measured* and relocated

The directive (originator): even at ∅-axiom, stop *borrowing kernel `Nat`*; stand on `Raw`.
First sharp target taken: **`isPart_wf` — Raw's own well-foundedness — re-proved without a
`Nat` depth measure**, by structural recursion on the slash-tree (`Raw.rec`) directly
(`Theory/Raw/Lambek.lean`, with helper `isPart_slash`). Atoms terminal
(`no_part_of_atom`), a slash's only parts its two children, each accessible by the
structural IH. Build green, `#print axioms`-clean.

**The honest, *measured* verdict (a constant-closure trace, not a slogan).** "`Nat`-free"
is not "axiom-free" — `Nat` is a definition, invisible to `scan_axioms`. So the closure of
used constants was traced directly:
- **`Raw.rec` (the structural recursor): 0 `Nat` constants.** The descent's *completion
  engine* is genuinely `Nat`-free — the recursion no longer elaborates against a borrowed
  `Nat` well-foundedness. This is the frontier's completion-engine criterion, met at the
  foundational layer for the first time *in the elaborated term*, not just morally.
- **Old proof (depth-measure cone, via `part_depth_lt`): 84 `Nat` constants.** The depth
  bound `r.depth < n` dragged in the whole `Tree.depth` / `Nat`-order machinery.
- **New proof: 17 `Nat` constants** — a real, measured drop (84 → 17 in the descent path),
  and a closure trace pins **all 17 to one source: `Raw.slash`**, the carrier's *canonical
  constructor* (`Tree`-comparison / `DecidableEq` for the `x ≠ y` ordering), inherited by
  `IsPart`'s very statement.

**What this relocated, and then closed.** The residual `Nat` was traced to
**canonicalization of `slash`** (Raw = `{ t : Tree // t.canonical = true }`; deciding the
`x ≠ y` order). Following that trace, the whole Raw foundational descent is **now
`Nat`-free** — measured **0 `Nat` constants** in the closures of `isPart_wf`, `Raw.rec` /
`Raw.recAux` (the structural recursor), `Raw.slash` (the carrier's canonical constructor),
and `IsPart`. The carrier, the recursor, and the well-foundedness all stand on the CIC
inductive kernel alone, no borrowed `Nat`.

The single root cause across all three layers was the kernel-generated
`Ordering.noConfusion`, which routes constructor-distinctness through
`Ordering.toCtorIdx : Ordering → Nat`. Every `cases h` on an `Ordering`-equality (to
discharge an impossible comparison branch) imported ~17 `Nat` constants. The fix
(`Term/Internal/Tree/Cmp.lean`): a `casesOn`-based discriminator `ordCode` / `ordNoConf`
(`Ordering.casesOn`/`rec` are themselves `Nat`-free), routed into:
- the `Tree.cmp` lemmas `cmp_eq_to_eq` / `cmp_gt_to_lt_swap` / `cmp_lt_to_gt_swap`;
- `Raw.slash_val_lt` / `slash_val_gt` (`Slash.lean`) — `Raw.slash`'s canonicalization;
- `Raw.recAux`'s canonicality threading (`Rec.lean`);
- the descent measure itself (`isPart_wf` re-grounded on `Raw.rec`, Round 5 head).
All four rewritten `rw`-free (the kernel-purity guard forbids `rw`; `Eq.subst`/`▸`,
`congrArg`, `.trans` used instead). Build green, `scan_axioms` PURE (no `propext`
introduced), closure-trace `Nat`-free.

So at the **`Raw` foundational layer the originator's directive is met**: stand on `Raw`,
do not borrow kernel `Nat`. Caveat held open per §5.1 / Round 2 sub-q 3: CIC itself is not
escaped — `Raw` is a kernel `inductive` (`Tree` + `Subtype` + `Bool`) — so the achieved bar
is "**one** inductive, `Raw`, every recursion structural on it, **no borrowed `Nat`**,"
verified by closure trace, not "0 kernel inductives" (empty, unreachable).

**The frontier above the foundation stays open.** This de-`Nat`s the `Raw`/`isPart_wf`
layer; it does **not** touch the disciplines built on borrowed `Nat` carriers (the additive
monoid on `List Unit`, FTA / `Ω` on kernel `Nat`, all of `Lib/Math`). Re-grounding *those*
on a `Nat`-free, `Raw`-native naturals object (the count-Lens image, not a `Nat` subtype)
remains the deep frontier — now with a proven technique (the `ordNoConf` pattern:
replace kernel auto-`noConfusion` with a `casesOn` discriminator) for peeling `Nat` out one
layer at a time, and a `Nat`-free foundation to build on.

**Round 6 — how far CIC itself can be peeled — is its own note** (`the_trusted_base.md`).
Verdict in brief: the trusted checker is irreducible (de Bruijn); "peel CIC to zero" is
empty. What is real and measured (`tools/cic_footprint.py`): the Raw cone restricts to a
*minimal CIC fragment* (one W-type `Tree`, `Tree.rec` structural recursion, no `Quot`/
`Classical`/`Acc`-elimination, `Nat`-free → verdict MINIMAL-STRUCTURAL), where the
disciplines above are EXTENDED-FRAGMENT (`WellFounded.rec`, `Nat.rec`, 158–218 `Nat`
constants). The footprint metric now *names the next lemma to de-CIC*, the same way the
`Nat`-trace named the next lemma to de-`Nat`.

## The exterior deliverable (the only §5.1-legal verdict)

Since the inside cannot self-certify primacy (§5.1), the one exterior-judgeable
artifact is the strict-∅-axiom, Mathlib-free, scanner-enforced corpus, pitched **not**
as "a new foundation" (un-judgeable) but as **axiom-base-minimization**, the sharpest
form being:

> A constructive corpus — FTA, Euclid's infinitude, divisibility — re-derived over a
> from-scratch naturals object, every theorem `#print axioms`-clean: no `propext`, no
> `Quot.sound`, no `Classical.choice`, no `native_decide`, **zero Mathlib** — *nothing
> beyond CIC's inductive kernel*. The axiom-base-minimization frontier for elementary
> number theory, mechanically audited.

This makes no primacy / no-exterior / forcing claim; an outside judge checks it with
`#print axioms`, `lake build`, `grep -r Mathlib`. The campaign against contingency,
cashed out in the one currency that needs no exterior: *provable axiom-emptiness*
(emptiness has no operand to dispute).

## Next-session deliverable (concrete)

Build the **completion-engine classifier**: a tool (grep over the proof cone +
`scan_axioms`, or a Lean meta-program) that reports, for a theorem, whether its
recursion completes through `Nat213.acc_lt` / `Raw`-native well-foundedness or the
borrowed kernel's `Nat.lt_wfRel` / `Nat.rec` on a `Nat` carrier. Validate against the
known split: descent-leg capstones (FTA over `Nat213`) should be native; a
re-derivation capstone (`quadratic_reciprocity`) should be borrowed. This *is* the
genesis metric, in its only defensible form. (Supersedes the PART-A
`tools/genesis_metric.py` sketch above, which the red-team retired.)

## Promotion status (closed part → permanent)

The *closed* part of this program — the generated ordered commutative semiring + the
operation tower + the ×-count-Lens and the exact +/× duality — is promoted to the
permanent chapter **`theory/math/numbersystems/arithmetic_generation.md`** (mirror of
the `Meta/Nat` generation files). This note now tracks only the **open frontier**: a
Raw-native *multiplicative descent* (prime-distinguishability / `exp`/`vp`) that would
let unique factorization (FTA) be *generated* rather than completed on the borrowed,
non-structural `Nat.strongRecOn` — the precise terminus of "generated vs borrowed."

## Progress — the descent measure made explicit (`MulDescentRec.lean`, PURE)

The multiplicative descent's well-order is now **named and used**, not left as the
opaque `strongRecOn`-over-magnitude.  `BigOmega` had shown the peel `n ↦ n/minFac n`
drops the prime-count by one (`Omega_descent`, the `×`-dual of `Raw.leaves`).
`Lib/Math/NumberTheory/MulDescentRec.lean` cashes that out as a **recursion
principle**:

  `mulDescentRec (P) (P 1) (∀ n≥2, P (n/minFac n) → P n) : ∀ n≥1, P n`

whose proof recurses on the **`Ω`-count** (`Nat.rec` over `Ω n`), each step justified
by `Omega_descent` — *not* `Nat.strongRecOn` over the magnitude `n`.  Demonstrated:
`mul_factorization_exists` (every `n≥1` a product of primes) proves *through*
`mulDescentRec`, the witness `minFac n :: …` peeled along the count-shadow.  Supporting
`Ω`-facts (`Omega_pos_of_two_le`, `eq_one_of_Omega_zero`, `quot_pos`) all PURE.  The
*uniqueness* face is paired in: `Omega_eq_length_of_prime_factorization` (every prime
factorization of `n` has length `Ω n` — `Ω` is the well-defined count, via
`factorization_unique` + `length_eq_of_countOcc_eq`), bundled with existence as
`fta_existence_and_count` — **FTA in count form** (existence = the descent/generation;
the shared length `Ω n` = the invariant the descent measures).

**Honest scope** (in-file): this does *not* escape CIC's `Nat.rec` — induction on the
count `Ω n` is `Nat.rec` on a `Nat`.  The exact, narrower claim: the **well-order
driving the peel is `Ω`** (a leaves-shadow), made explicit, replacing the opaque
magnitude `strongRecOn`.  Still open: a descent whose *carrier* (not just measure) is
Raw-native — `factorize` itself is fuel-recursion on the magnitude.

## Cross-refs

- `research-notes/frontiers/the_descent_leg.md` — the one genuine generation arc
  (FTA over `Nat213`); the "recognition not genesis" honest wall.
- `research-notes/frontiers/the_substance_test.md`,
  `the_purpose_and_the_marathon.md` — prior 진의 inferences (this note advances them).
- `seed/AXIOM/05_no_exterior.md` §5.1 (no self-certification), §5.2 (Bool- vs
  Nat-style self-reference — the *form* of completion), §5.4 (CeilingSchema guard).
- `lean/E213/Lib/Math/Foundations/CeilingSchema.lean` — apparent ceilings = internal
  non-surjections; the schema that converts "wall" into "internal missing target."
- `papers/the_residue_of_distinguishing.md` §3, §8 — the conceded limits this program targets.
