# The 213 Decomposition Calculus — a human-facing technique for *seeing* mathematics

**Status**: new research cluster (Tier 1, actively evolving — the shape *will* change as we
practice; that is expected). This is the **originator's central direction**: not "re-derive classical
theorems in Lean" (that is scaffolding) but *create a way of doing/describing mathematics* — the way
category theory created objects/arrows/functors, type theory created types/terms/judgments — and then
**decompose existing mathematics into it**. Raw/Lens are the *Lean encoding* (the machine verifier);
**this is the form a human reads and writes.** 0-axiom is just the discipline the purpose forces.

## What it is

Every mathematical object is a **construction read through a lens**; every theorem is a **property of
a reading**. The calculus writes any piece of mathematics in one normal form:

```
   OBJECT   =   ⟨ C | L ⟩                 C = Construction,  L = Reading
   RESIDUE(L,C)  =  what L forces but cannot capture
   THEOREM:  P(⟨C | L⟩)                    "read C through L and property P holds"
```

- **Construction `C`** — the *distinguishing-history*: what was distinguished from what, iterated.
  The bare generative act, before any feature is chosen. (Lean shadow: a `Raw` / a generation rule.)
- **Reading `L`** — the *Lens*: which feature of the construction you project to — count, order,
  difference, divisibility, parity, ratio, …. A choice of *what to keep and what to forget*. (Lean
  shadow: a `Lens`, i.e. `Raw → α`.)
- **Residue** — what the reading *forces but does not capture*: the surplus a chosen Lens leaves
  un-pointed (often the gap that drives the next concept — e.g. the reals are the residue of the
  rational-approximation reading).

## The decomposition procedure ("to 213-decompose X")

1. **Find the construction.** Strip X to the bare distinguishings that generate the objects it talks
   about. Ask: *what is distinguished from what, and iterated how?*
2. **Name the reading.** Which feature does X actually *use*? (Often X is stated as if about "the
   objects" when it is really about *one projection* of them.)
3. **Locate the residue.** What does this reading force but not capture?
4. **Re-see the theorem, and look for collapse.** Rewrite X as `P(⟨C | L⟩)`. Then ask the
   load-bearing question: *does another, superficially different theorem have the same `(C, L)`?* If
   so they are **one theorem**; that collapse is the payoff.

## The revelation rule (the re-skin guard — non-negotiable)

A decomposition that only *re-describes* X in new words is worthless — it is exactly the
"abstract nonsense" jeer category theory survived, and this repo's own audit verdict ("genuinely new
mathematics: none"). The category theory analogy is the warning *and* the way out: CT was accepted
because its notation eventually **paid** (Yoneda, adjoints, the functor of points let you *do* new
things). So every decomposition must end with an explicit **Revelation** — one of:

- **collapse** — two/many apparently-different things shown to be one `(C, L)`;
- **forcing** — a feature shown to be *forced* by `C` (not an arbitrary choice);
- **residue surfaced** — a concept re-identified as the residue of a reading (so "irrational",
  "infinite", "continuous" stop being separate realms and become *shapes of a reading's surplus*);
- **substance/notation collapse caught** — a place where a Reading had been mistaken for a substance,
  or a Construction-tuple for its flattened readout.

If a decomposition has no Revelation, it is re-skin; drop it or dig deeper. **Lean's role**: verify
the collapse/forcing is *real* (a proven kernel-equality / homomorphism), not asserted — the
honesty-check, not the deliverable.

## Why this is not invented from nothing: the failure-mode catalog *is* this technique's shadow

The strongest evidence the calculus is real: the repo *already lives by it* — negatively. Nearly every
entry in CLAUDE.md's "Failure modes catalog" is **a botched or missed 213-decomposition** — someone
treated a *Reading* as a substance, or a *Construction-tuple* as its flattened readout, or the
*Residue* as a god above the finite. Crystallizing the positive method makes the catalog's discipline
constructive instead of corrective:

| Failure mode (the miss) | The decomposition it failed to do |
|---|---|
| "ℤ / sign as exterior import" | `ℤ = ⟨ directed count-pair `(m,n)` ∣ difference-reading `m−n` ⟩`; sign = pair-swap, not a Raw primitive (`practice/integers.md`) |
| "Equivalence-pluralism" (동치/동형/준동형 as 4 things) | one Lens-arrow `Lens.refines`; the four are facets of `⟨ two Raws ∣ a reading `L` ⟩` (`practice/equivalence.md`) |
| "Quotient promoted to ontology" (the lowest-terms fraction is "the real number") | the *tuple is the object*; `ratio` is a Reading; reduction = *applying* the Lens (flattening the kernel), never the default |
| "Limit/infinity deified" | `lim` = the *residue* of an approximation-reading; its finite signature (the modulus) is the operand, the limit never is |
| "`^`-wall diagnosed via `log`" | the log is an exterior ruler; the `^`-inverse is the **cut** reading; folding decided in the ×-count reading (`exp`) |
| "0/∞ as a stratum-value" | `0`/`∞` = one pre-Lens residue; "value" vs "limit" is a mixed-status reading error |

So the catalog is the *list of ways people fail to decompose*; the calculus is *how to decompose*.

## The practice (this is the research)

The unit of progress is **one worked decomposition with a verified Revelation**. The practice
notebook (`practice/`) decomposes existing mathematics one piece at a time, recording the Revelation
and citing the Lean theorem that certifies it. First batch (crystallizing scattered repo
decompositions into the one procedure):

- `practice/parity.md` — parity, congruence, permutation-sign, `det = ±1` as **one**
  construction-preserving finite reading (Lean: `ModArith.Zolotarev`).
- `practice/integers.md` — ℤ as the difference-reading of a directed count-pair; "negative" is not a
  substance (Lean: `Nat213.Tower.NatPairToInt.npairToInt = Int.subNatNat`).
- `practice/equivalence.md` — 동치 / 동치류 / 동형 / 준동형 = one Lens-arrow (Lean:
  `Lens.refines`, `Unified.lensIso_iff_kernel_eq`).

Then: **fresh** decompositions (math the repo has *not* pre-chewed) — where the technique must
*generate* the seeing, not recall it. That is the real test of the tool.

## Refinements from the first practice batch (the shape changed, as expected)

The first six decompositions (`practice/`) each *forced* an answer to a design question. The calculus,
refined by practice:

**`C` (Construction) carries optional read-off sub-structures — not one flat axis:**
- **direction / swap-bit** → read out as *sign* (ℤ, `integers.md`) and *orientation*; a `Bool`-style
  pair-swap, not a Raw primitive.
- **fold-height / depth** → read out as *dimension / degree / pole-order / nesting* (`dimension.md`).
  **Verdict: first-class** — it pays by collapse (four notions = one height-reading) and is *forced*
  (the well-founded measure already in `C`: `Lambek.isPart_wf`, `Factorization.acc_lt`), so the
  reading only reports what the build had to carry.
- **atom-(in)distinguishability** → the single axis whose two poles are the *scalar* +-construction
  (units indistinguishable, `UnitList.append_comm`) and the *vector* ×-construction (primes
  distinguishable, `FoldCriterion.two_three_unique`) — i.e. *why* multiplication has a per-prime axis
  and addition does not (`prime_factorization.md`).

**`L` (Reading) carries parameters — it is not just a projection:**
- a **resolution** parameter: the *same* Lens at "adjacent = step `1`" (discrete) vs "adjacent via a
  modulus, `h→0`" (residue) unifies `Δ`/`d` and `Σ`/`∫` (`derivative.md`); the limit is never the
  operand, only its finite modulus is.
- a **character / logarithmic** mode: a construction-preserving reading whose readout may *change the
  operation* (`×`↦`+`, `vp_mul`) — generalizing the finite-cyclic "character" of `parity.md` to a free
  ℕ-module readout (`prime_factorization.md`).

**Residue is first-class, and stratifies:** the normal form is really `⟨C | L⟩ ⊕ Residue(L,C)`, the
residue *generated by the reading's own self-application* (`cardinality.md`: the diagonal is `t(f a a)`
— the count-reading re-entering itself; this is §1.0′'s proof-primitive for the infinite). It
*stratifies*: a per-reading residue can be trivial/faithful (the prime-valuation reading is injective,
`vp_separation`/`eq_of_vp_eq`) even while the *global* self-cover non-surjection (`object1_not_surjective`)
is not — "no residue here" and "always a residue globally" coexist.

**One emerging map** (to test further): `C` = distinguishing + {direction, height, atom-distinguishability};
`L` = a reading + {resolution, character-mode}; `Residue` = `L`'s self-application surplus. The deepest
collapses so far sit where two of these meet — `L₋` (difference) where direction (C) meets resolution
(L) gives ℤ *and* the derivative; the count-reading + its residue gives all the limitative theorems.

## Refinements from the second batch (determinant, golden ratio, exponential, continuity)

The fresh batch sharpened the model further:

- **A *character* is a reading whose readout is itself a number-construction** carrying `C`'s own
  direction+height sub-structure (magnitude = the count it scales, sign = the orientation it
  preserves/flips). `det` is exactly this — `det(MN)=det M·det N` (`det2_mul`) is the character `×↦·`,
  with `det=±1` being `parity.md`'s `L₂` and general `det` its multiplicative-scalar extension
  (`determinant.md`). So "character" subsumes parity, sign, det, Legendre — one pattern.
- **Character-mode is *bidirectional*** — a reading `×↦+` (valuation/log) and its inverse `+↦×` (exp)
  are *one arrow with a direction toggle* (which operation is operand vs readout); the residue (the
  `^`-wall, the transcendental `e`) sits *between the two directions*, where faithfulness
  (`vp_separation`) meets the wall (`two_three_unique`) (`exponential.md`).
- **★ The Residue carries a multiplier bit `q = ±1`** — the single biggest structural find. The
  *escaping* residue (Cantor's diagonal, fixed-point-free, oscillates *outside* every reading) and the
  *converging* residue (φ, has a fixed point, asymptotes *toward* one) are **the same residue at the
  two unimodular poles** `q = −1` vs `q = +1` (`CassiniUnimodular.cassini_law_one_at_two_multipliers`,
  `OneDiagonal.no_surjection_of_fixedpointfree`). So `cardinality.md`'s diagonal and `golden_ratio.md`'s
  φ are one object: `Residue(L,C)` should be written with a **`q=±1` tag** = oscillate-outside (q=−1) /
  asymptote-to-fixed-point (q=+1). This is the calculus's deepest collapse: the limitative theorems and
  the golden ratio are one residue read at its two signs.
- **Resolution is an *organizing axis*, not just a parameter** — promoting `L`'s resolution dial to a
  *condition* gives a whole discipline: **topology = the three questions of the dial** — does it commute
  with refinement (continuous map), is its fibre refinement-stable (open set), what is its residue
  (limit point) (`continuity.md`; `IsContinuousModulus`, `uniform_limit_continuous`, `DyadicOpen`, and
  `four_way_modulus_framework` — one modulus structure carries continuity + derivative + Ricci + α_em).

**Updated map**: `C` = distinguishing + {direction, height, atom-distinguishability}; `L` = a reading +
{resolution (→ a whole discipline when made a condition), character-mode (bidirectional)}; `Residue` =
`L`'s self-application surplus, tagged `q = ±1` (escape / converge). Every deepest result sits where two
of these meet. Open Lean targets surfaced: `continuous_iff_preimage_dyadicopen`; a formal `q=±1`
residue tag uniting `object1_not_surjective` and the φ Cassini law. (See
`research-notes/frontiers/decomposition_calculus.md`.)

Next: keep decomposing **fresh** mathematics and let it break/extend this map (groups/symmetry,
probability/measure, homology, the Galois correspondence, …).
