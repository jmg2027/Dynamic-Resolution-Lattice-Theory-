# G206 — pre-registered probe of the alternative-REFRAME direction (Line B(b)); NULL result

A **pre-registered, time-boxed** attack on the residual Markov-uniqueness kernel isolated in `G204`
— the Line B(b) item of `the_substance_test.md` (external exposure: a falsifiable bet on a
recognized open problem, registered *before* the run so the outcome cannot be retro-fitted). This
note records the bet, the test, and the **null result** (the honest outcome), with the computational
evidence. It does not close the conjecture and never claimed it would.

## Why pre-register

The substance test (`the_substance_test.md`) is "is no-exterior/primacy substance or wordplay,
*without self-deception*". The §5.1 blind spot is that the framework cannot falsify itself from
inside. The disciplined external move on an open problem is to **state the bet and the kill
criterion in advance**, run once, and report whatever happens — so a null result is data, not a
moved goalpost. This is the opposite of accumulating another perimeter restatement and calling it
progress (the failure mode `G204` warns against).

## The target (from G204, unchanged conjecture)

Markov uniqueness (Frobenius 1913) for the **residual kernel**: composite `c` with ≥ 2 distinct odd
prime factors `≡ 1 mod 4` (so `x²≡−1 mod c` has ≥ 4 roots) **and** both `3c−2`, `3c+2` composite
(so the Zhang modulus-shift `9c²−4 = (3c−2)(3c+2)` has no prime-power factor to read through).
`G202`/Agent-B verdict: the realized vs phantom roots are indistinguishable by every elementary
congruence; the separator is fundamental-unit / class-number data of discriminant `9c²−4`.

## The pre-registered bet (direction #1 of G204)

> **H1 (universal alternative reframe).** There is a single linear form `M(c) = αc + β`
> (small `α, β`) that, for *every* residual `c`, is a prime power — giving a Zhang-style
> root-count reframe that fires uniformly where `3c±2` fails.

Falsification criterion, fixed in advance: H1 is **rejected** if no `(α,β)` in the box
`1 ≤ α ≤ 12, |β| ≤ 12` makes `αc+β` a prime power for all residual `c` up to the enumeration bound.
Secondary registered checks: **H4** (does an *order* invariant separate realized from phantom within
each `{u, c−u}` pair?) and **H3** (does an *iterated* reframe through the tree-neighbours `a,b` of
`c` supply a prime-power modulus uniformly?).

Time-box: one session; one enumeration + battery. Stop condition: report on first decisive
rejection or confirmation. (Probe code: `/tmp/markov_probe{,2,3}.py`, reproducible — Vieta-tree
generation + `sympy.factorint`.)

## Result — NULL (H1 rejected; H3/H4 do not separate)

Enumerated all Markov numbers and their realized roots via the Vieta tree; residual cases:
**9 with `c ≤ 2·10⁵`, 33 with `c ≤ 10⁹`** (610, 1325, 6466, 9077, 10946, 37666, 51641, 62210,
196418, 499393, …, 647072098).

| registered check | outcome |
|---|---|
| **H1** universal prime-power `αc+β`, `1≤α≤12,|β|≤12` | **NONE** — over all 9 (`≤2·10⁵`) *and* all 33 (`≤10⁹`) residual `c`. Rejected at scale. |
| **H2** per-`c` prime-power linear forms exist? | Yes (6–18 per `c`), but each lacks the Zhang gap-identity `(3c−2)(ab)=(b−a)²+c²` that makes the modulus *fire*. Prime-power-ness is necessary, not sufficient — these are not usable reframes. |
| **H3** iterated reframe via neighbours `a,b` | Neighbour-moduli `3a±2, 3b±2, a, b` are *often* prime powers (for `c=6466`, all six are), but no firing identity through a neighbour was exhibited; the neighbours' own uniqueness is already given by tree-induction and does not constrain `c`'s root fiber. Not a separator. |
| **H4** order separation within `{u,c−u}` | NO — the realized minimal-rep is sometimes smaller (`10946, 51641`), sometimes larger (`610, 1325, …`) than the phantom reps. No order monovariant. |

Observed structure (not a separator, recorded): realized and phantom roots each come in `{u, c−u}`
pairs; the Fibonacci-spine residual `c` (610, 10946, 196418, …) have realized roots equal to adjacent
Fibonacci numbers (matches `MarkovUniqueness.fib_spine_sqrt_neg_one`).

## Conclusion — the honest output

The probe **confirms `G204`/`G202` computationally**: no elementary universal invariant (linear
reframe, order, or single-step neighbour reframe) separates realized from phantom roots across the
residual family, now checked to `10⁹`. Direction #1 as stated is **falsified**; the separator is not
elementary, consistent with the class-number / fundamental-unit verdict. This is a **negative
result**, registered and reported as such — it sharpens where elementary methods provably stop, and
it is *not* progress toward the conjecture (the irreducible kernel `H` remains untouched, exactly as
`G204` states).

Value to the substance test: this is the framework being **honest under an external, falsifiable
test it could have passed and did not** — the §5.1 blind-spot discipline working as intended. A
restatement dressed as progress would have been the self-deception the test exists to catch.

## Surviving (non-elementary) directions — unchanged from G204 #2/#3

- **Conditional formalization**: record `uniqueness ⟸ [explicit fundamental-unit condition on
  9c²−4]` as an `∅`-axiom reduction, isolating the exact non-elementary input. Honest; does not close.
- **The genuine core**: class-number / fundamental-unit content of `9c²−4` — the 110-year-open
  conjecture itself; out of elementary reach.

## Pointers
- Residual definition + proven side: `G204_post_zhang_residual.md`.
- Number-theory verdict (class-number separator): `G202_zhang_3c_pm2_roadmap.md`.
- Substance-test frame (Line B): `research-notes/frontiers/the_substance_test.md`.
