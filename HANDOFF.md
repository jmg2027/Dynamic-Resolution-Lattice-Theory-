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
  * **lcm valuation** (next, the companion to `legendre`) — `vₚ(lcm 1..N) =
    (max j with p^j ≤ N)`.  Build: (a) `lcmUpTo : Nat → Nat` (`lcmUpTo (n+1) =
    lcm213 (n+1) (lcmUpTo n)`, `lcmUpTo 0 = 1`); (b) `vp_monotone`
    (`a∣b → 0<b → vₚa ≤ vₚb`, from `le_vp_iff`); (c) `vp_gcd_min`/`vp_lcm_max`
    via `vp_monotone` + `Lcm213.gcd_mul_lcm` + `vp_mul` (avoid vp-of-quotient by
    using the product identity `gcd·lcm = a·b`).  **CAVEAT**: `Nat.min_eq_right`,
    `Nat.min_zero` carry **propext** — phrase max/min explicitly (`if e ≤ f then
    f else e`) or prove the needed `(e+f) - min e f = max e f`-shape by hand.
  * **FTA-lite** — `(∀ prime power q, q∣a → q∣b) → a∣b` (prime-factor enumeration
    up to `n`).
  * **Steps 2–7** — key divisibility (compare the two sides' `vₚ` via `legendre`
    + lcm valuation, folding the floor terms through `count30` at
    `m̃=⌊30m/p^{j+1}⌋`), factorial-ratio bound (`α₃₀ = 2¹⁴3⁹5⁵`), recursion,
    numeral induction (`37·α₃₀⁶ ≤ 10⁷⁵` by decide on the big literal), main
    `lcm(1..30m) ≤ 10^{15m}`, corollaries `lcm⁶ ≤ 10^{87+3n}`.

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
lean/E213/Lib/Math/NumberTheory/LcmGrowthChebyshev.lean  ← NEW (§1 count30)
lean/E213/Lib/Math/NumberTheory/PrimeValuation.lean      ← NEW (vp_mul, prime_dvd_mul, Prime213)
lean/E213/Lib/Math/NumberTheory/Legendre.lean            ← NEW (legendre full formula; vp_factorial, vp_one, val_count, indLt_sum, div_succ_increment)
research-notes/frontiers/zeta3_blueprint.md              ← formalization-progress section (Legendre done)
```
