# G204 — post-Zhang residual: the Markov frontier after the prime-power-neighbour families close

Standing record of the Markov uniqueness frontier (`markov_lagrange/` topic) **after** the prime-power
families closed `∅`-axiom this branch.  Supersedes the "reduce to one realizability hypothesis `H`" framing
of `G173`: several infinite families are now *closed*, and the residual is sharply the class-number core.

## Closure record (∅-axiom, `lean/E213/`) — the proven side

| family | theorem | route |
|---|---|---|
| odd prime power `pᵏ` (Button) | `SternBrocotMarkov.markov_prime_pow_unique` | c-side ≤ 2 roots |
| even `2·pᵏ` | `SternBrocotMarkov.markov_two_prime_pow_unique` | CRT recombination (`MarkovPrimeFactor.two_roots_of_two_prime_pow`) |
| `3c±2` a prime power (Zhang) | `MarkovUniqueness.markov_max_unique_via_3c_pm2` | modulus shift `9c²−4 = (3c−2)(3c+2)`; gap (`3c−2`) / sum (`3c+2`) |
| concrete `985 = 5·197` | `MarkovUniqueness.markovMaxUnique_985` | Zhang `3c−2 = 2953` prime |

Distance-1 cross-line `SEPARATE`: `SternBrocotMarkov.markovNum_children_ne` (forced, all nodes).  Order
exhaustion: `markovNum_subtree_size_interleaves` (§36 — no order-monovariant separates cross-line).

## The residual open frontier (sharpened)

**Core open problem (unchanged conjecture):** Markov uniqueness (Frobenius 1913) — each max `c`
determines a unique triple.  **What is now isolated as the hard residue:**

> Composite `c` with `≥ 2` distinct odd prime factors `≡ 1 mod 4` (so `x²≡−1 mod c` has `≥ 4` roots)
> **and** both `3c−2`, `3c+2` composite (so no modulus-shift presentation collapses the fiber).  Smallest:
> `c = 1325 = 5²·53` (`3c−2 = 29·137`, `3c+2 = 41·97`).

Established this branch (deep number-theory reading, `G202`): the discriminator between realized and
phantom roots is **not elementary** — both ±-pairs pass every congruence/representation test; the
separation is a global Vieta-descent orbit condition under the units of the order of discriminant `9c²−4`,
i.e. **class-number / fundamental-unit data**.  No congruence in the prime factors decides it.  This is the
genuine Frobenius core; elementary methods provably stop here.

## The tool and its limit — REFRAME

The modulus shift is the `REFRAME` lift archetype (`G203`, `ProofISALifts.lift_reframe_modulus`): factor a
shared invariant (modulus `2pᵏ` / discriminant `9c²−4`) and read through the prime-power factor where a
solved `SEPARATE` fires.  **Conditional**: needs a prime-power factor.  Exhausted exactly at the residual
above (no good factor) — which is *why* `1325` is hard for Zhang too.

## Live directions (ranked, honestly)

1. **More REFRAME factors** — is there a *different* invariant (not `9c²−4`) for `c` whose factorisation
   has a prime-power piece where `9c²−4` does not?  Or an *iterated* reframe (read through a deeper Vieta
   ancestor)?  Speculative; the natural next probe.
2. **Conditional formalization** — record `uniqueness ⟸ [class-number condition X]` as an `∅`-axiom
   reduction, isolating the exact non-elementary input.  Honest but does not close.
3. **The genuine core** — class-number / fundamental-unit content of `9c²−4`.  Out of elementary reach;
   the 110-year-open conjecture itself.

## Pointers
- Proven side: theorems above (`SternBrocotMarkov`, `MarkovUniqueness`, `MarkovPrimeFactor`).
- Narrative arc: `G196`–`G203` (top-level) — ISA localization → families → Zhang → REFRAME.
- Promotion due: the closed `pᵏ / 2pᵏ / 3c±2` arc → `theory/` chapter (mirrors `Lib/Math/.../Markov*`).
