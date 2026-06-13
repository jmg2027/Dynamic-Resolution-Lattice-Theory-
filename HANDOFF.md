# Session Handoff — 2026-06-13

## Branch
`claude/pnt-continuation-k1eerf` — main merged in, working tree clean,
`lake build` (full project, 441 modules) green, strict ∅-axiom intact.
Marathon complete; **READY TO MERGE** to main (push + merge is the final step).

## What Was Done This Session — the PNT continuation

The prime-counting trajectory was carried past the (previously-closed) density
cut + Chebyshev lower bound to its ∅-axiom-reachable boundary, plus the
de-deification calculation principle and a structural identity.

### 1. Two-sided Chebyshev order theorem + the constant as a computable interval (PURE)
`Lens/Number/Nat213/ChebyshevLower.lean`:
- **`chebyshev_order`** — `π(2^{m+1}) = Θ(2^{m+1}/m)`, both halves in one explicit
  division-free statement (`2^{m+1} ≤ 2(m+2)·π`, `(m+1)·π ≤ 6·2^{m+1}`), via the
  factor lemmas `two_pow_le_succ_primePi` / `succ_mul_primePi_pow_two_le`.
- **`chebyshev_constant_interval`** — the PNT-direction constant `log₂e ≈ 1.4427`
  trapped in the computable interval `[(m+1)/(2(m+2)), 6]`, evaluable at every `m`,
  narrowing from below.

### 2. The `→1` pointing shape `RatTendsToOne` (PURE)
`MultSystemValue.lean`: `RatTendsToOne` (two-sided `→1` ε-δ modulus, companion of
`RatTendsToZero`'s `→0`) + `RatTendsToOne.within` (soundness) + `succOverSelf`
(`(N+1)/N→1` validation).  Records the shape of the PNT pointing without an
external value.

### 3. lcm-form (ψ) lower + central-binomial↔lcm bridge (PURE)
`ChebyshevLower.lean`: **`central_binom_dvd_lcm`** (`C(2n,n) ∣ lcm(1..2n)`, via
`dvd_of_forall_vp_le` + `vp_lcmUpTo`) ⟹ **`two_pow_le_lcm`** (`2^n ≤ lcm(1..2n)`,
i.e. `ψ(2n) ≥ n·ln2`).  Used `le_of_dvd_pos`, not the propext-tainted `Nat.le_of_dvd`.

### 4. The structural one-shot — factorial↔lcm exponent identity (PURE, new file)
`Lib/Math/NumberTheory/FactorialLcmIdentity.lean` (7 PURE / 0 dirty):
**`vp_factorial_eq_sum_vp_lcm`** — `vₚ(N!) = Σ_{i=1}^N vₚ(lcm(1..⌊N/i⌋))`, the
exponent form of `N! = Π lcm(1..⌊N/i⌋)`.  Legendre read as a Fubini count on
`{(i,j): i·pʲ ≤ N}`.  Reusable ∅-axiom infra built here: `sumTo_fubini`,
`count_lt_le`, `count_div`, `sumTo_extend_vanish`.  Wired into CI via `ChebyshevLower`.

### 5. De-deification: "infinity is the residue's shape" as a *calculation rule*
`theory/essays/foundations/the_form_of_the_residue.md` (new section) + CLAUDE.md
failure-row "Limit/infinity deified".  Originator correction: conceiving infinity
is itself a discrete pointing; the residue arises *because the framing produces it*
(`object1_not_surjective` is a theorem about the self-cover's construction); so the
limit/constant is the *computed bracket*, not a target — the modulus/bracket is the
operand 213 calculates with.

### 6. Marathon wrap (skill sequence)
merge main · `/process` (sink 0 violations, frontier INDEX refreshed) · promotion
(chebyshev chapter clause/row upgrades, log #82) · cross-domain resonances (R1/R2,
PNT ↔ merged logarithm-family) · `/essay` (`the_prime_constant_is_archimedean`,
essays 99→100, log #83) · `/org-audit` (orphan 0, hygiene 0) · `/purity-check`
(strict ∅-axiom) · `/ready-to-merge` (fixed 1 stale `SpiralRotationInvariant` ref
from main's clustering; READY).

## Current Precision Results
Unchanged this session (pure number-theory / foundations work; no physics constants
touched).  See `catalogs/physics-constants.md`.

## Open Problems (Priority Order)
### 1. PNT proper `π(N) ~ N/ln N` (constant `1`) — the archimedean horizon
Not ∅-axiom reachable: the constant is the slope at the *single archimedean place*
(`ψ(N)=Σ vp_p(lcm)·ln p`), while every reachable handle lives at the algebraic `vp`
places.  Recorded as the computable-interval horizon (the bracket is the math).
Frontier: `research-notes/frontiers/multiplicative_count_pnt.md`.

### 2. Sharpen the constant interval to `[2, 3.16]` (∅-axiom reachable)
(i) base-`2` lower via the max-binomial `4^n ≤ (2n+1)·C(2n,n)` (`C(2n,n) ≥ 4^n/(2n+1)`);
(ii) matching upper base `≈ 3.16` by unwinding `LcmGrowthChebyshev`'s 30-block
recurrence (`step4`, `alpha30`) to a closed `lcm(1..N) ≤ C·base^N`.
Frontier: `research-notes/frontiers/multiplicative_count_pnt.md`.

### 3. The operation-tower object re-foundation — build `UnitHyper` (carried forward)
The generative `^`-object (free semigroup over the `×`-cone, the dilation/dimension
axis) is unbuilt.  Frontier: `research-notes/frontiers/simplicial_operation_tower.md`.

## Unresolved from This Session
- The constant `1`/`e` is genuinely PNT-strength (Selberg–Erdős/analytic), not
  central-binomial reachable — confirmed structural, not a gap to grind.  The
  interval-narrowing (Open #2) is the honest ∅-axiom continuation.

## Next
Pick up Open #2 (base-`2` max-binomial lower is the lighter of the two — needs
binomial unimodality `4^n ≤ (2n+1)·C(2n,n)`), or Open #3 (`UnitHyper`).

## Three-tier state
- **Promotions this session**: `chebyshev_prime_counting.md` ← the order/interval +
  lcm-form + factorial↔lcm layer (clause/row upgrades in place, log #82); essay
  `the_prime_constant_is_archimedean.md` (log #83).
- **Promotion candidates**: none pending — the PNT trajectory's ∅-axiom-reachable
  results are all reflected in the chapter; the constant is an open frontier.
- **Active scratchpad**: `frontiers/multiplicative_count_pnt.md` (interval sharpening
  + cross-domain resonances), `frontiers/simplicial_operation_tower.md`.

## File Map
```
lean/E213/Lens/Number/Nat213/ChebyshevLower.lean      ← chebyshev_order, constant interval, ψ-lower, lcm bridge
lean/E213/Lens/Number/Nat213/MultSystemValue.lean     ← RatTendsToOne (+within, succOverSelf)
lean/E213/Lib/Math/NumberTheory/FactorialLcmIdentity.lean ← NEW: vp_factorial_eq_sum_vp_lcm + sumTo_fubini/count_div infra
theory/math/numbertheory/chebyshev_prime_counting.md  ← order section + table rows (promotion)
theory/essays/synthesis/the_prime_constant_is_archimedean.md ← NEW essay (#100)
theory/essays/foundations/the_form_of_the_residue.md  ← "calculation rule" de-deification section
research-notes/frontiers/multiplicative_count_pnt.md  ← PNT horizon + interval sharpening + R1/R2 resonances
```
