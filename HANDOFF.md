# Session Handoff — 2026-06-04 (Markov composite uniqueness: prime-power-neighbour families)

## Branch
`claude/markov-uniqueness-0R0Ut` — 3 commits ahead of `origin` (the process/essay/org-audit marathon
commits); the math commits are pushed.  `cd lean && lake build E213` ✓ clean.  About to push + merge to
`main`.

## What was done this session

### 1. New infinite composite-uniqueness families closed (all strict ∅-axiom)
`MarkovMaxUnique c` (the Markov uniqueness conjecture at a fixed max `c`) is now closed unconditionally for
two families beyond Button's odd prime powers:

- **Even `2·pᵏ`** — `SternBrocotMarkov.markov_two_prime_pow_unique`, via CRT recombination of the root
  count (`MarkovPrimeFactor.two_roots_of_two_prime_pow`: `x²≡−1 mod 2·pᵏ` has ≤ 2 roots, the factor 2
  split off by CRT).  Covers even Markov numbers `34 = 2·17`, `194 = 2·97`, …
- **Zhang's `3c±2` criterion** — `MarkovUniqueness.markov_max_unique_via_3c_pm2`: if `3c−2` **or** `3c+2`
  is an odd prime power, `c` is unique.  Mechanism: the discriminant `9c²−4 = (3c−2)(3c+2)` is read mod the
  prime-power factor, collapsing the c-side `≥ 4`-root reading to `≤ 2` (`MarkovPrimeFactor.sq_eq_collapse_pp`).
  `3c−2` reframes through the **gap** `b−a`, `3c+2` through the **sum** `a+b`.
  Concrete: **`markovMaxUnique_985`** — first composite Markov number (`985 = 5·197`, 4 roots) closed
  **structurally, no `decide` on the triple** (`3·985−2 = 2953` prime; `√2953`-bounded primality via
  `prime_of_no_small_factor`).

Supporting ∅-axiom chain (in `MarkovUniqueness` / `MarkovPrimeFactor`): `zhang_linear_core`,
`zhang_quadratic(_sum)`, `zhang_gap_dvd` / `zhang_sum_dvd`, `zhang_gap_determines_pair` /
`markov_sum_determines_pair`, `markov_sum_le_max` (`a+b ≤ c`), `sq_collapse_pow_ordered`.

### 2. The kernel localized + the REFRAME archetype
- `SternBrocotMarkov.markovNum_children_ne` — distance-1 cross-line `SEPARATE` (every node's two children
  have distinct Markov numbers), uniformly, by a trace monovariant.
- `markovNum_subtree_size_interleaves` — the order-monovariant is exhausted past distance 1 (sizes
  interleave across the fork), so the residue is not size-shaped.
- **REFRAME** = fourth proof-ISA lift archetype (`Foundations/ProofISALifts.lift_reframe`): factor a shared
  invariant, read through the prime-power factor where `SEPARATE` fires.  CRT (`2·pᵏ`) and the modulus shift
  (`3c±2`) are one move at two layers.  Essay: `theory/essays/methodology/reframe_presentation_transport`.

### 3. Marathon (process / essay / org-audit / purity / ready-to-merge)
- process: sink-rule 0 violations; post-Zhang frontier recorded (`G204`).
- essay + promotion: REFRAME methodology essay; `theory/math/analysis/markov_uniqueness.md` status updated
  with the closed families.
- org-audit: STRICT_ZERO_AXIOM gained the composite-uniqueness families addition; narrative clean, no orphans.
- purity-check: 0 sorry / axiom / native_decide / Classical; headline capstones strict ∅-axiom.
- ready-to-merge: layer violations 0; kernel pure 45/45; verdict READY.

## Open Problems (priority order)

### 1. The genuine Frobenius core — composite `c` with both `3c±2` composite
Smallest `c = 1325 = 5²·53` (`3c−2 = 29·137`, `3c+2 = 41·97`).  No modulus-shift presentation collapses
the fiber, and no order-monovariant separates the roots (`§36`).  The realized/phantom discriminator is the
**class-number / fundamental-unit content** of the order of discriminant `9c²−4` — genuinely non-elementary
(established this branch).  Frontier note: `research-notes/frontiers/markov_lagrange/G204_post_zhang_residual.md`.

### 2. Extend REFRAME (the reachable next probe)
Is there a *different* carried invariant (not `9c²−4`) for `c` whose factorisation has a prime-power piece
where `9c²−4` does not, or an *iterated* reframe through a deeper Vieta ancestor?  Conditional; speculative.
Frontier note: `research-notes/frontiers/markov_lagrange/G204_post_zhang_residual.md` (Live directions §1).

## Unresolved from this session
- Full Frobenius uniqueness is **not** solved (it is the 110-year-open conjecture; the class-number core is
  out of elementary reach — this is established, not a gap to retry).
- No concrete `c` exhibited where `3c+2` is prime but `3c−2` composite (the `3c+2` half is proven generally;
  a demo instance wasn't searched — `markovMaxUnique_985` already demos the `3c−2` half).

## Next
- Push the 3 marathon commits + **merge to `main`** (the marathon's final step).
- Then: REFRAME-extension probe (Open Problem 2), or move to a different domain (primacy = breadth).

## Three-tier state
- **Promotions this session**: `theory/math/analysis/markov_uniqueness.md` (status updated, closed families)
  + `theory/essays/methodology/reframe_presentation_transport.md` (new essay).
- **Promotion candidates**: the closed Markov families are now reflected in the chapter; no further
  promotion outstanding for this arc.
- **Active scratchpad**: `research-notes/G196`–`G203` (top-level) record the arc (ISA localization →
  families → Zhang → REFRAME); the open frontier lives in `frontiers/markov_lagrange/G204`.

## File Map
```
lean/E213/Lib/Math/NumberSystems/Real213/MarkovUniqueness.lean   ← Zhang 3c±2 (both halves + unified),
                                                                   sum/gap helpers, markovMaxUnique_985
lean/E213/Lib/Math/NumberSystems/Real213/SternBrocotMarkov.lean  ← markov_two_prime_pow_unique, §35/§36
lean/E213/Lib/Math/NumberTheory/ModArith/MarkovPrimeFactor.lean  ← two_roots_of_two_prime_pow,
                                                                   sq_eq_collapse_pp, prime_of_no_small_factor
lean/E213/Lib/Math/Foundations/ProofISALifts.lean                ← REFRAME archetype (lift_reframe*)
theory/essays/methodology/reframe_presentation_transport.md      ← REFRAME methodology essay
theory/math/analysis/markov_uniqueness.md                        ← status updated (closed families)
research-notes/frontiers/markov_lagrange/G204_post_zhang_residual.md ← open frontier (class-number core)
research-notes/G196–G203_*.md                                    ← the arc's working notes
STRICT_ZERO_AXIOM.md                                             ← composite-uniqueness families addition
```
