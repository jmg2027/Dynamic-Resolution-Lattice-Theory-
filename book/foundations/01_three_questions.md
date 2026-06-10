# Chapter 1 — Three questions about a tower

The number systems arrive, in every textbook, as a staircase: the naturals, then the
integers, then the rationals, then the reals.  `seed/AXIOM/06_lens_readings.md` §6.7
re-reads that staircase 213-natively — not as four imported types but as **successive
bundlings of one residue under different Lens choices**:

> the slash, read by the count-Lens `⟨1, 1, +⟩`, gives `ℕ`; the count-Lens read on an
> ordered pair, its sign the period-2 swap `−(−x) = x`, gives `ℤ`; ratios of chain
> readings, their lowest-terms condition the unit `det P = NS − NT = 1`, give `ℚ`;
> Cauchy trajectories of those readings, narrowing to a single cut, give `ℝ`.

`book/` took that staircase and *climbed* it — read the orbit, the Cassini unit, the
disc edifice as a readout sitting three Lens-steps up.  This volume turns around and
looks *down* at the staircase itself.  Three questions.

## 1.1 Is the tower complete?

"Complete" has a trap in it.  The classical answer — *the reals are Cauchy-complete,
so the tower stops at `ℝ`* — imports the very metric closure it is trying to justify.
And the staircase visibly does *not* stop in the usual telling: `ℝ → ℂ → ℍ → 𝕆`
continues, the Cayley–Dickson doubling, four more "number systems."  So which is it —
does the tower close at `ℝ`, or does it run `ℕ, ℤ, ℚ, ℝ, ℂ, ℍ, 𝕆, …`?

The 213-native form of the question is sharper, and it has an answer the codebase can
witness.  *Is the bundling operation — count, then difference, then ratio, then
completion — at a fixpoint when it reaches `ℝ`?*  If applying the operation once more
returns `ℝ`, then `ℝ` is where *this* operation closes, and anything past it is a
*different* operation.  Chapter 2 shows that is exactly the situation: `ℝ` is a
Cauchy fixpoint (PROVED), and `ℝ → ℂ` is a categorically different step — the
dimension-doubling axis, not the readout-bundling chain.

## 1.2 Is it one axis, or several serialized?

The staircase is drawn as a line.  But the four steps are not the same operation
iterated.  Counting reads **breadth** — how many leaves the slash-chain has.  The
difference-Lens closes the count under **additive** inverse (`m − n`, sign the period-2
swap).  The ratio-Lens closes it under **multiplicative** inverse (`p/q`, lowest
terms).  The Cauchy step is not an algebraic closure at all — it is a **limit**.

Additive-inverse and multiplicative-inverse closure are two *different* directions.
Drawing them as one line — `ℤ` then `ℚ`, `+/−` before `×/÷` — is a serialization.  Is
it a *forced* serialization (the residue insists on this order) or a *conventional*
one (the residue admits a lattice of readings and we walked one path through it)?
Chapter 3 finds the latter: the substrate is a lattice of Lens refinements, the linear
tower is one chain through it, and `ℤ` and `ℚ` are independent enough that the `ℚ`
founding does not even *cite* the `ℤ` one.

## 1.3 Is each step forced?

§6.7 says **choices**.  The word is deliberate and it is the crux.  A choice implies
alternatives; if the count-Lens, the difference-Lens, the ratio-Lens, the Cauchy
completion are *choices*, then the tower is one selection from a space of towers, and
no rung is privileged — exactly the discipline of `seed/AXIOM/05_no_exterior.md` and
the "View promoted to identity" failure mode (CLAUDE.md,
`FlatOntologyClosure.object1_not_surjective`): a reading is a facet, not the thing.

But some rungs may be *more* forced than others.  The count `⟨1, 1, +⟩` may be the
unique first Lens (an initiality question — `Theory.Raw.CoResidue`, Lambek).  The
period-2 sign may be forced by `NT = 2` rather than chosen.  Chapter 4 grades each
rung FORCED / CHOICE / OPEN.

## 1.4 The discipline: no exterior to measure "complete / one / forced" against

A standing caution, because all three questions invite a smuggled comparison frame.

"Complete" tempts a comparison to some ambient totality the tower is supposed to fill
out — but there is no exterior totality (`05_no_exterior.md` §8.1).  Completeness can
only mean an *internal* fixpoint: the operation returns its own codomain.  "One axis"
tempts a fixed coordinate system to count axes in — but the axes are *themselves* Lens
readings; "how many axes" is a question about the Lens lattice, answered inside it, not
from a vantage above it.  "Forced" tempts a notion of necessity borrowed from outside
213 — but the only necessity available is *the residue admits no other reading at this
rung*, which is again an internal, witnessable statement (or an honest OPEN).

So every answer in this volume is of one shape: **a fact about the residue read
through its own Lenses**, never a fact about how the tower sits in something larger.
Where no such internal fact is available, the entry is OPEN, not guessed.
