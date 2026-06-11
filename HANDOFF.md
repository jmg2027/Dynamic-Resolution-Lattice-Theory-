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

9. **`LcmGrowthChebyshev.lean` §5–§7 — STEP 2 CLOSED**: pure div cancellation
   (`mul_div_mul_left_pure`, `le_div_iff_mul_le`, `le_of_mul_le_mul_right'`),
   `perLevel` (per-prime-power inequality = `count30` at `m̃=⌊30m/d⌋`), and
   **`key_divisibility`**: `lcm(1..30m)·(15m)!(10m)!(6m)! ∣ (30m)!·m!·lcm(1..5m)`.
   Via FTA-lite per prime → `vp_mul`+`legendre`+`vp_lcmUpTo` to `Σ_{e<30m}` (common
   bound via `sumTo_extend`) → `perLevel` summed by `sumTo_le_sumTo`.  ∅-axiom.

## ★★★ Brick 1 (the lcm race, input I2) is COMPLETE — all 7 steps PURE
`count30` (step 1) · `key_divisibility` (step 2) · `step3` (factorial-ratio bound) ·
`step4` (recursion `lcm(30m) ≤ (6m+1)·α₃₀^m·lcm(5m)`) · `step5` (numeral induction) ·
**`main`** `lcm(1..30m) ≤ 10^{15m}` · **`lcmUpTo_le`** `lcm(1..n) ≤ 10^{15⌈n/30⌉} ≈
(√10)ⁿ < 3.236ⁿ = α^{1/3·n}` — the ζ(3) lcm-race deliverable.

Modules: `LcmGrowthChebyshev.lean`, `PrimeValuation.lean`, `Legendre.lean`,
`FTALite.lean`, `FactorialRatioBound.lean` (the rediscovered B1·B2 decomposition +
`choose_absorb` unimodality), `LcmBoundMain.lean` (steps 5–7).

∅-axiom traps logged: `α₃₀` `[local irreducible]` (whnf explodes in defeq/`ring_nat`);
`ring_nat` deep-recurses on **literal-exponent** `^` terms → prove reassoc on opaque
variables (`re1`-style) and instantiate; base certs `decide` need `maxRecDepth`/
`maxHeartbeats` raised (`lcmUpTo 750 ≤ 10^375` ~1s); `Nat.le_of_add_le_add_right`,
`Nat.add_sub_cancel*`, `Nat.{pow_add,mul_pow,pow_mul,div_div_eq_div_mul}` all carry
`propext` → pure replacements built.

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
`cd lean && lake build E213.Lib.Math.NumberTheory.LcmBoundMain` (pulls the whole
Brick-1 chain); `python3 tools/scan_axioms.py <module>` → all PURE.

## File Map (Brick 1 — all NEW, all PURE)
```
lean/E213/Lib/Math/NumberTheory/LcmGrowthChebyshev.lean  ← §1 count30; §2 lcmUpTo; §3 vp_lcmUpTo+floorLog; §4 div_div_pure,sumTo_le_sumTo; §5–§7 perLevel/key_divisibility; §8 step4_cleared; §9 alpha30,pow30_eq,step4
lean/E213/Lib/Math/NumberTheory/PrimeValuation.lean      ← vp_mul, prime_dvd_mul, Prime213; vp_monotone, vp_gcd_min, vp_lcm_max
lean/E213/Lib/Math/NumberTheory/Legendre.lean            ← legendre (full formula); vp_factorial, val_count, indLt_sum, div_succ_increment
lean/E213/Lib/Math/NumberTheory/FTALite.lean             ← dvd_of_forall_prime_vp_le
lean/E213/Lib/Math/NumberTheory/FactorialRatioBound.lean ← step3 (factorial-ratio bound) + B1/B2 + choose_absorb + tcoef machinery
lean/E213/Lib/Math/NumberTheory/LcmBoundMain.lean        ← step5; main (lcm(1..30m)≤10^{15m}); lcmUpTo_le (the deliverable)
research-notes/frontiers/zeta3_blueprint.md              ← Brick 1 COMPLETE marked
```
