# Session Handoff — 2026-06-12 (ζ(3) Brick 2: KeyDiv + Heart CLOSED)

## This session (2026-06-12): Brick 2 §2–§4 — all PURE
`AperyIntegrality.lean` now **31 PURE / 0 dirty**.  Landed, in order:

  * **§2 KeyDiv COMPLETE** — `keydiv : m·C(k,m) ∣ lcm(1..k)` (`1≤m≤k`).
    `keydiv_prod` (`m·C(m+s,m)·s! = rprod m (s+1)`, bridge) · `rprod_split` ·
    `Qex_mul` (`(m+j)·Qex m s j = rprod m (s+1)`) · `LPos`/`LNeg` (even/odd
    quotient sums) · `dfd_pos`/`dfd_neg` (`d·fdPos = rprod·LPos`) · `keydiv_dvd`
    (generic `(∀j≤s,(m+j)∣d) → m·C(m+s,m)∣d`; `fd_identity`×`d`, cancel `s!` ⟹
    `P·LPos = d + P·LNeg` ⟹ `d = P·(LPos−LNeg)`).  Built on the prior-session
    `fd_identity` (the FD identity, even/odd Nat, no `Int`).
  * **§3 Heart (L2) COMPLETE** — `heart : m·C(k,m)∣d → m³·C(n,m)·C(n+m,m) ∣
    d³·C(n,k)·C(n+k,k)`.  `d = m·C(k,m)·Q` into the cube; `aperyTrinomial`
    collapses `C(k,m)²·C(n,k)·C(n+k,k)`; witness `Q³·C(k,m)·C(n−m,k−m)·C(n+k,n+m)`
    (needs only KeyDiv — simpler than the `Q²·R` blueprint sketch).
  * **§4 engines** — `cube_dvd_lcm_cube` (`j³∣lcm(1..n)³`, harmonic) + `heart_lcm`
    (`m³C(n,m)C(n+m,m) ∣ lcm³C(n,k)C(n+k,k)`, Heart at `d=lcm(1..n)`).

### Traps hit this session
  * `Nat.dvd_trans` carries **propext** → inline transitivity via the two dvd
    witnesses (`rcases ⟨u,hu⟩, ⟨v,hv⟩; exact ⟨u*v, by rw…; ring_nat⟩`).
  * `ring_nat` on literal-exponent `^` → local `cube x : x^3 = x*x*x`
    (`Nat.pow_succ`×2 + `Nat.pow_one`); rewrite all `^3/^2` to products first.
  * `m+(s+1)` vs `m+s+1` not closed by `rw`'s rfl → `Nat.add_succ` to normalise.

### §4 REMAINING (the ÷-free alternating-sum assembly) + FINAL assembly
See `research-notes/frontiers/zeta3_blueprint.md` "Brick 2 … §4 REMAINING".
Short form: define `Aₙ = 2·lcm³·aₙ`, `Bₙ` as Nat/signed sums; harmonic terms clear
by `cube_dvd_lcm_cube`, kernel terms by `heart_lcm`; signs ⟹ pos/neg Nat split
(`Int` banned).  Then connect `(Aₙ,Bₙ)`↔`zeta3Num/zeta3Den` (recurrence ↔ sum),
`2lcm³∣(n!)³` (`n≥4`), piecewise `(c,p,q)`, `htel` from `lcmUpTo_le` vs
`zeta3Den_geom` ⟹ `zeta3_reduced_conditional` ⟹ `zeta3HolonomicReal`.

---

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

## Next: Brick 2 (Apéry integrality, input I1) — STARTED
Brick 2 = `2·lcm(1..n)³·aₙ ∈ ℕ`, "pure divisibility chains, NO p-adics".
  * **§1 DONE + PURE** — `AperyIntegrality.lean` `aperyTrinomial`: the trinomial
    double identity `C(n,k)C(n+k,k)C(k,m)² = C(n,m)C(n+m,m)C(n−m,k−m)C(n+k,n+m)`
    (additive form `n=m+a+b,k=m+b`; both sides clear by `a!(m!)²(b!)²` to
    `(2m+a+2b)!` via telescoping `choose_mul_factorials`).
  * **§2 KeyDiv** (IN PROGRESS, `AperyIntegrality.lean` §2–§3 — 14 PURE atoms built)
    — `m·C(k,m) ∣ lcm(1..k)` via `FD(m,s) := Σ_{j≤s}(−1)ʲC(s,j)·Qex m s j = s!`.
    **Built**: `rprod` (rising factorial) + `rprod_front/back/one/pos`; `Qex m s j =
    rprod m j·rprod (m+j+1)(s−j)` (= `Π_{i∈[0,s],i≠j}(m+i)`) + **`Qex_back`**
    (`Qex m (s+1) j = (m+s+1)Qex m s j`, `j≤s`), **`Qex_front`** (`Qex m (s+1)(j+1) =
    m·Qex (m+1) s j`), `Qex_self` (`Qex m s s = rprod m s`); even/odd sums
    **`fdPos/fdNeg m s = Σ_{j even/odd,≤s} C(s,j)Qex m s j`** + base (`fdPos m 0=1,
    fdNeg m 0=0`).
    **REMAINING — the recurrence system** `(P) fdPos(m,s+1)=(m+s+1)fdPos(m,s)+
    m·fdNeg(m+1,s)`, `(N) fdNeg(m,s+1)=(m+s+1)fdNeg(m,s)+m·fdPos(m+1,s)`.
    **Fully-derived additive proof of (P)** (no Nat subtraction): `sumTo_split_first`
    peels `j=0`: `fdPos(m,s+1) = g 0 + Σ_j g(j+1)`, `g 0 = (m+s+1)·Qex m s 0`
    (`Qex_back`, `C(s+1,0)=1`); pointwise `g(j+1) = m·[j%2=1]C(s,j)Qex(m+1)s j +
    (m+s+1)·[(j+1)%2=0]C(s,j+1)Qex m s(j+1)` (Pascal `choose_succ_succ` + `Qex_front`
    on the `C(s,j)` part, `Qex_back` on the `C(s,j+1)` part; the `(j+1)%2=0`-case needs
    a sub-case `j+1≤s` vs `j=s` where `C(s,s+1)=0` & `Qex_self`+`rprod_front`);
    `sumTo_add_func` ⟹ `Σ g(j+1) = m·fdNeg(m+1,s) + (m+s+1)·S2`, and `S2 + Qex m s 0
    = fdPos(m,s)` (`sumTo_split_first`, the `j=s` term of `S2` is 0).  Then induction
    `fdPos = s! + fdNeg` (from (P)−(N), the `fdNeg` terms cancel: `(m+s+1)s!−m·s!=
    (s+1)!`).  **CAVEAT**: pure mod-2 needed — `Nat.{mod_two_eq_zero_or_one,add_mod}`
    carry propext; build `(j+1)%2=0 ↔ j%2=1` from `Nat.mod_lt`+`div_add_mod_pure`.
    Then KeyDiv from FD via the lcm combination (next).
    --- (original route note) ---
    Route (no primes): the
    finite-difference identity `FD(m,s) := Σ_{j≤s}(−1)ʲC(s,j)·Π_{i≠j}(m+i) = s!`.
    **Clean recurrence derived** (de-risks the build): from the partial-fraction
    telescoping `T(m,s+1)=T(m,s)−T(m+1,s)` (`T(m,s)=Σⱼ(−1)ʲC(s,j)/(m+j)=s!/Π(m..m+s)`,
    Pascal `C(s+1,j)=C(s,j)+C(s,j−1)` + reindex `j↦i+1`), clearing by `Π_{i=0}^{s+1}(m+i)`:
    ```
    FD(m,s+1) = (m+s+1)·FD(m,s) − m·FD(m+1,s),  FD(m,0)=1  ⟹  FD(m,s)=s!
    (base s+1: (m+s+1)·s! − m·s! = (s+1)·s! = (s+1)!).
    ```
    (Lean `Int` is **unusable** — `Int.{add,mul,add_mul,sub_self}_*` all carry
    `propext`; so use `Int213` or the even/odd Nat split below.)
    Encode the signed `FD` as **even/odd Nat sums** `pos(m,s)=Σ_{j even}C(s,j)Q,
    neg(m,s)=Σ_{j odd}C(s,j)Q` and prove `pos = s! + neg` (avoids `Int`); `Q(m,s,j)
    = Π_{i≤s,i≠j}(m+i)` (product-excluding-`j`, the awkward bit — encode as
    `Π_{i<j}(m+i)·Π_{j<i≤s}(m+i)` or `P/(m+j)` exact division).  Then KeyDiv:
    `lcm + m·C(k,m)·negW = m·C(k,m)·posW` (`posW/negW = Σ_{even/odd j}C(k−m,j)·
    lcm/(m+j)`, each `lcm/(m+j)∈ℕ` via `dvd_lcmUpTo`, `m+j≤k`) ⟹ `m·C(k,m) ∣ lcm`.
    ~200-line fresh build.  Have: `aperyTrinomial`, `choose`/Pascal (`choose_succ_succ`),
    `choose_mul_factorials`, `lcmUpTo`/`dvd_lcmUpTo`, `sumTo`.
  * **§3 Heart (L2)** — `m³C(n,m)C(n+m,m) ∣ d³·C(n,k)C(n+k,k)` (`d=lcm`): divide
    `aperyTrinomial` in; remainder `Q²·R·C(n−m,k−m)·C(n+k,n+m)`, `Q=d/(mC(k,m))`,
    `R=d/m` integers by KeyDiv.
  * **§4 Assembly** — termwise with the `C(n,k)²C(n+k,k)²` prefactor; the `2`
    cancels `2m³` → `2·lcm³·aₙ ∈ ℕ`.

## Then: the final assembly → `zeta3HolonomicReal`
Feed **I1** (integrality) and **I2** (= the new `LcmBoundMain.lcmUpTo_le` against
the orbit growth `Zeta3Cut.zeta3Den_geom`, as the `htel` margin) into
`Zeta3Cut.zeta3_reduced_conditional`, then build the `CauchyCutSeq` (modulus
`N(m,k)=k+n₀+2`) and `HolonomicReal` (template: `ExpLog/EulerModulus.eHolonomicReal`).
**Clearing-bridge subtlety** (flagged turn 1): the conditional needs
`zeta3Num = c·p`, `zeta3Den = c·q` ∀ n with `(p,q)=(Aₙ,dₙ)=(2lcm³aₙ,2lcm³bₙ)`;
`c n = (n!)³/(2lcm³)` is integral only for `n ≥ 4` (`2lcm³ ∣ (n!)³` ⟺ `n!/lcm`
even, holds `n≥4`), so define `(c,p,q)` **piecewise** (`n≤3`: `c=1,p=zeta3Num,
q=zeta3Den`; `n≥4`: the reduced pair) and take the `htel` from `n₀ ≥ 4`.

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
lean/E213/Lib/Math/NumberTheory/LcmBoundMain.lean        ← step5; main (lcm(1..30m)≤10^{15m}); lcmUpTo_le (Brick 1 deliverable)
lean/E213/Lib/Math/NumberTheory/AperyIntegrality.lean    ← Brick 2 §1: aperyTrinomial (trinomial double identity)
research-notes/frontiers/zeta3_blueprint.md              ← Brick 1 COMPLETE; Brick 2 §1 done
```
