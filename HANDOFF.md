# Session Handoff — 2026-06-11 (ζ(3) Brick 1 marathon, opened)

## Branch
`claude/zeta3-apery-integrality-y9jy1x` — pushed work in progress.  This is the
ζ(3) `HolonomicReal` route: discharge the two classical inputs of
`Zeta3Cut.zeta3_reduced_conditional` (I1 integrality, I2 lcm race), then
instantiate to get `zeta3HolonomicReal` unconditional.

## What Was Done This Session — Brick 1 foundation (lcm bound), bottom-up

Three PURE (∅-axiom) modules landed, in dependency order.  Each builds + scans
PURE individually.

1. **`Lib/Math/NumberTheory/LcmGrowthChebyshev.lean` §1 — `count30`**
   Brick 1 step 1: the 30-periodic counting lemma
   `[m̃≥1]+⌊m̃/2⌋+⌊m̃/3⌋+⌊m̃/5⌋ ≤ m̃+⌊m̃/30⌋+[m̃≥6]` for **every** `m̃`.
   Proof by the `30q+r` split (`r<30`): the `q`-coefficients are `15+10+6 = 31`
   (left) and `30+1 = 31` (right) — they cancel, leaving the residue inequality
   (decided on the 30 residues).  No induction.

2. **`Lib/Math/NumberTheory/PrimeValuation.lean` — `vp_mul`**
   `vₚ(a·b) = vₚa + vₚb` at a prime (`a,b>0`).  `Prime213 p := 2≤p ∧ (∀d,
   d∣p → d=1 ∨ d=p)`.  Euclid's lemma `prime_dvd_mul` (p∣ab → p∣a ∨ p∣b) routed
   through the Bezout-free `Gcd213.coprime_dvd_of_dvd_mul`.  The gear Legendre
   turns on.

3. **`Lib/Math/NumberTheory/Legendre.lean` — `legendre`** (full formula)
   **`vₚ(n!) = Σ_{j<n} ⌊n/p^{j+1}⌋`** (`p` prime), ∅-axiom — the crux of Brick 1.
   Half 1 `vp_factorial` (`vₚ(n!) = Σ_{k<n} vₚ(k+1)`, additivity via `vp_mul`) +
   half 2 by the **increment route, no Fubini**: induction on `n`, LHS gains
   `vₚ(n+1)`, RHS gains `Σⱼ[p^{j+1}∣n+1] = vₚ(n+1)`.  Helpers (all PURE):
   `div_succ_increment` (`⌊(n+1)/d⌋=⌊n/d⌋+[d∣n+1]` via `div_eq_of_sandwich`),
   `val_count` (`Σ_{j<B}[p^{j+1}∣m]=vₚm` via `le_vp_iff`+`indLt_sum`),
   `indLt_sum` (`Σ_{j<B}[j<V]=V`), `top_vanish`, `lt_of_mul_lt_mul_left'`,
   `sumTo_const_one/zero`.

4. **`PrimeValuation.lean` §3 — `vp` on gcd/lcm** (`vₚ` is a valuation):
   `vp_monotone` (`a∣b → vₚa ≤ vₚb`); `vp_gcd_min` (`vₚ(gcd a b)=min`, explicit
   `if`); **`vp_lcm_max`** (`vₚ(lcm a b)=max`) from `vₚ(gcd)+vₚ(lcm)=vₚ(a·b)`
   (`gcd_mul_lcm`+`vp_mul`) cancelling `vₚ(gcd)=min` — product identity, no Nat
   subtraction.  `add_left_cancel_pure` (core `Nat.add_left_cancel` is propext).

5. **`LcmGrowthChebyshev.lean` §2 — iterated lcm**: `lcmUpTo N = lcm(1..N)`,
   `lcmUpTo_pos`, `dvd_lcmUpTo` (`k∈[1,N] → k∣lcm`), `lcmUpTo_dvd` (universal
   property — the step-6 divisibility certificate).

6. **`LcmGrowthChebyshev.lean` §3 — lcm valuation as a count**: **`vp_lcmUpTo`**
   (`vₚ(lcm 1..N) = Σ_{e<N}[p^{e+1}≤N]`, `p` prime) — the lcm-side companion to
   `legendre`.  Built on the `floorLog` theory (mirror of `vpSearch`): the sandwich
   `p^{floorLog}≤N<p^{floorLog+1}`, the bridge `p^{e+1}≤N ↔ e<floorLog`
   (`pow_le_iff_lt_floorLog`), `lcmExpCount_eq_floorLog`, pure pow strict-mono.

7. **`FTALite.lean` — `dvd_of_forall_prime_vp_le`**: **`(∀ prime p, vₚa≤vₚb) →
   a∣b`** (`a,b>0`) — contrapositive of the existing `ModArith.ValuationAlg.
   exists_prime_vp_gt` (same `vp`; `Prime213` matches its prime predicate).

8. **`LcmGrowthChebyshev.lean` §4 prep**: `div_div_pure` (`n/(a·b)=n/a/b`, pure
   nested floor) + `sumTo_le_sumTo` (termwise Σ-monotonicity).

### Note: pre-existing `vp_mul` in `ModArith/ValuationAlg.lean`
`ValuationAlg.vp_mul` (unbundled `hpr` arg) duplicates `PrimeValuation.vp_mul`
(bundled `Prime213`).  Mine is the clean bundled API used downstream; the dup is a
minor org-audit item, not blocking.

### ∅-axiom traps hit (intel for next session)
  - `Nat.div_add_mod`, `Nat.pow_add`, `Nat.mul_mul_mul_comm` all carry
    **propext** — use `NatDiv213.div_add_mod_pure`, and a pure `pow_add`/
    4-factor swap built from `NatHelper.mul_assoc`/`mul_left_comm`.
  - `by_contra` is a **Mathlib** tactic (unavailable) — use `le_vp_iff`'s
    contrapositive / `Nat.lt_of_not_le` + `Nat.le_of_lt_succ`.
  - `by_cases h : p ∣ a` uses the **propext-carrying** `Decidable (·∣·)` —
    case on `a % p = 0` (pure `decEq`) instead, bridge with
    `AddMod213.dvd_of_mod_eq_zero` / `Valuation.mod_zero_of_dvd`.
  - `rw [hu]` where `hu : a = …` rewrites `a` **inside** `vp p a` too
    (proliferates `a`) — rewrite the product *back* to `a` with `← hu` inside a
    `calc`, or `generalize` the exponent first.
  - `ring_nat` treats `p ^ vp p a` / `Nat.succ k` as **opaque atoms** and
    breaks on `+0`/`0+`/`0*`/`1*` — use explicit `Nat` lemmas for pow/factor
    reshuffles.

## Remaining chain to close Brick 1 (frontier: `zeta3_blueprint.md`)
**All four hard gates are cleared** — `count30`, `legendre`, `vp_lcmUpTo`,
`dvd_of_forall_prime_vp_le` (FTA-lite) — plus §4 plumbing (`div_div_pure`,
`sumTo_le_sumTo`).  What remains is assembly (no new deep math).

  * **Step 2 — key divisibility** (next): `lcm(1..30m)·(15m)!(10m)!(6m)! ∣
    (30m)!·m!·lcm(1..5m)`.  Via FTA-lite, suffices `∀ prime p, vₚ(LHS) ≤ vₚ(RHS)`.
    Expand each side with `PrimeValuation.vp_mul` (additivity; factors are
    `lcmUpTo_pos`/`factorial_pos`), rewrite factorials by `legendre` and lcms by
    `vp_lcmUpTo` → both sides become `Σ_e` of per-level terms.  Extend all sums to a
    common bound `30m` (extra terms vanish — a sum-extension lemma).  Per level
    `d=p^{e+1}`, with `m̃=⌊30m/d⌋`: `⌊15m/d⌋=⌊m̃/2⌋`, `⌊10m/d⌋=⌊m̃/3⌋`,
    `⌊6m/d⌋=⌊m̃/5⌋`, `⌊m/d⌋=⌊m̃/30⌋` (via `div_div_pure` + `(c·x)/(c·y)=x/y`),
    `[d≤30m]=[m̃≥1]`, `[d≤5m]=[m̃≥6]`; then per level it is exactly `count30 m̃`,
    summed by `sumTo_le_sumTo`.  Sub-lemmas to build: sum-extension; `(c·x)/(c·y)=x/y`
    pure; the `[d≤k·m]↔[m̃≥…]` indicator mappings.
  * **Steps 3–7** — factorial-ratio bound (`α₃₀ = 2¹⁴3⁹5⁵`, three binomial-term
    bounds), recursion `lcm(1..30m) ≤ (6m+1)·α₃₀^m·lcm(1..5m)` (step 2 + 3), numeral
    induction (`37·α₃₀⁶ ≤ 10⁷⁵` by `decide`), main `lcm(1..30m) ≤ 10^{15m}`,
    corollaries `lcm⁶ ≤ 10^{87+3n}`.

## Then: Brick 2 (Apéry integrality) + assembly
Brick 2 (`zeta3_blueprint.md` Brick 2) is "pure divisibility chains, NO p-adics"
— trinomial double identity + KeyDiv via the finite-difference witness — likely
**more** ∅-axiom-tractable than Brick 1 (no prime infra), despite more lines.
Assembly: feed I1 (integrality factorization `zeta3Num = c·p`, `zeta3Den = c·q`)
and I2 (the `htel` margin from `lcm < α^{1/3}ⁿ` vs the orbit's `28`-geometric
growth `zeta3Den_geom`) into `Zeta3Cut.zeta3_reduced_conditional`, then build the
`CauchyCutSeq` (modulus `N(m,k)=k+n₀+2`) and the `HolonomicReal` (template:
`ExpLog/EulerModulus.eHolonomicReal`).

## Engine end (already closed, prior session)
`Zeta3Cut.zeta3_reduced_conditional` consumes I1+I2 and yields the constructed
total modulus; `aperyOrbit_geom`/`zeta3Den_geom` (28>27=3³ race margin);
localization `(601/500, 1203/1000]`.  See `Zeta3Cut.lean` §8–§9.

## Verify
`cd lean && lake build E213.Lib.Math.NumberTheory.{LcmGrowthChebyshev,PrimeValuation,Legendre}`;
`python3 tools/scan_axioms.py <module>` → all PURE.

## File Map
```
lean/E213/Lib/Math/NumberTheory/LcmGrowthChebyshev.lean  ← NEW (§1 count30; §2 lcmUpTo; §3 vp_lcmUpTo + floorLog; §4 div_div_pure, sumTo_le_sumTo)
lean/E213/Lib/Math/NumberTheory/PrimeValuation.lean      ← NEW (vp_mul, prime_dvd_mul, Prime213; §3 vp_monotone, vp_gcd_min, vp_lcm_max)
lean/E213/Lib/Math/NumberTheory/FTALite.lean             ← NEW (dvd_of_forall_prime_vp_le)
lean/E213/Lib/Math/NumberTheory/Legendre.lean            ← NEW (legendre full formula; vp_factorial, vp_one, val_count, indLt_sum, div_succ_increment)
research-notes/frontiers/zeta3_blueprint.md              ← formalization-progress section (Legendre done)
```
