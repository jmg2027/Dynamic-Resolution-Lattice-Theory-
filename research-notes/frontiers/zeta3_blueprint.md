# ζ(3) free modulus: the verified proof blueprint (both bricks)

**Status**: no open mathematics left — formalization plans only.  Produced by a
multi-agent derivation round; **every load-bearing claim independently
re-verified by exact integer computation** (ranges per item).  Companion to
`zeta3_free_modulus.md` (which states the problem and the clearing-growth
criterion forcing these two bricks).

## Formalization progress (Brick 1, bottom-up)

PURE (∅-axiom) modules landed, in dependency order:

  * `Lib/Math/NumberTheory/LcmGrowthChebyshev.lean` §1 — **`count30`** = Brick 1
    step 1, the 30-periodic counting lemma `[m̃≥1]+⌊m̃/2⌋+⌊m̃/3⌋+⌊m̃/5⌋ ≤
    m̃+⌊m̃/30⌋+[m̃≥6]` for every `m̃` (30q+r split; q-coeffs 31=31 cancel).
  * `Lib/Math/NumberTheory/PrimeValuation.lean` — **`vp_mul`** = `vₚ(a·b)=vₚa+vₚb`
    at a prime (`Prime213`), with Euclid's lemma `prime_dvd_mul` via the
    Bezout-free `Gcd213.coprime_dvd_of_dvd_mul`.  The gear under Legendre.
  * `Lib/Math/NumberTheory/Legendre.lean` — **`legendre`** = the full factorial
    formula `vₚ(n!) = Σ_{j<n} ⌊n/p^{j+1}⌋` (`p` prime).  Half 1 (`vp_factorial`,
    additivity over the product) + half 2 (the double-counting, via the increment
    route — `div_succ_increment` `⌊(n+1)/d⌋=⌊n/d⌋+[d∣n+1]` summed + `val_count`
    `Σ_{j<B}[p^{j+1}∣m]=vₚm`, no Fubini swap).  Helpers: `indLt_sum`,
    `sumTo_const_one/zero`, `lt_of_mul_lt_mul_left'`, `top_vanish`.

PURE landed since: `PrimeValuation.lean` §3 (`vp_monotone`, `vp_gcd_min`,
`vp_lcm_max`); `LcmGrowthChebyshev.lean` §2 (`lcmUpTo` + universal property), §3
(**`vp_lcmUpTo`** = `vₚ(lcm 1..N) = Σ_{e<N}[p^{e+1}≤N]`, via the `floorLog`
sandwich), §4 (`div_div_pure`, `sumTo_le_sumTo`); `FTALite.lean`
(**`dvd_of_forall_prime_vp_le`** = `(∀ prime p, vₚa≤vₚb)→a∣b`, contrapositive of
the repo's `exists_prime_vp_gt`).

### ★★★ Brick 1 (the lcm race, input I2) is COMPLETE — all 7 steps PURE.

Modules: `LcmGrowthChebyshev.lean` (§1 `count30`; §2 `lcmUpTo`; §3 `vp_lcmUpTo`;
§5–§7 `perLevel`/`key_divisibility`; §8 `step4_cleared`; §9 `step4`),
`PrimeValuation.lean` (`vp_mul`, `vp_lcm_max`, …), `Legendre.lean` (`legendre`),
`FTALite.lean` (`dvd_of_forall_prime_vp_le`), `FactorialRatioBound.lean` (`step3` =
factorial-ratio bound, with the rediscovered B1·B2 decomposition + `choose_absorb`
unimodality), `LcmBoundMain.lean` (`step5` numeral induction, **`main`**
`lcm(1..30m) ≤ 10^{15m}`, **`lcmUpTo_le`** `lcm(1..n) ≤ 10^{15⌈n/30⌉} ≈ (√10)ⁿ`).

The deliverable is `LcmBoundMain.lcmUpTo_le` (√10 < 3.236 = α^{1/3}).  Remaining for
ζ(3): **Brick 2 (integrality, input I1)** + assembly into `zeta3HolonomicReal`.

### ★★★ Brick 2 (integrality, input I1) — §1–§3 COMPLETE + PURE; §4 engines landed

All in `Lib/Math/NumberTheory/AperyIntegrality.lean` (31 PURE / 0 dirty):

  * **§1 `aperyTrinomial`** — the trinomial double identity (both sides clear to
    `(2m+a+2b)!`).
  * **§2 KeyDiv COMPLETE** — `keydiv : m·C(k,m) ∣ lcm(1..k)` (`1≤m≤k`).  Built from
    the finite-difference identity `fd_identity : fdPos m s = s! + fdNeg m s`
    (i.e. `Σⱼ(−1)ʲC(s,j)·Πᵢ≠ⱼ(m+i) = s!`, even/odd Nat split, induction via the
    `(P)/(N)` recurrences `fdPos_succ`/`fdNeg_succ`).  Bridge `keydiv_prod :
    m·C(m+s,m)·s! = rprod m (s+1)`.  Then `rprod_split`, `Qex_mul` (excluded factor
    restored), `LPos`/`LNeg` (even/odd quotient sums `ΣC(s,j)(d/(m+j))`),
    `dfd_pos`/`dfd_neg` (`d·fdPos = rprod·LPos`), `keydiv_dvd` (generic: `(∀j≤s,
    (m+j)∣d) → m·C(m+s,m)∣d`, by `fd_identity`×`d`, cancel `s!` ⟹ `P·LPos = d +
    P·LNeg` ⟹ `d = P·(LPos−LNeg)`).  **No `Int`, no p-adics** — even/odd Nat throughout.
  * **§3 Heart (L2) COMPLETE** — `heart : m·C(k,m)∣d → m³·C(n,m)·C(n+m,m) ∣
    d³·C(n,k)·C(n+k,k)`.  Substitute `d = m·C(k,m)·Q` into the cube; `aperyTrinomial`
    collapses the `C(k,m)²·C(n,k)·C(n+k,k)` block; witness `Q³·C(k,m)·C(n−m,k−m)·
    C(n+k,n+m)` (needs only KeyDiv, **not** a separate `d/m` — simpler than the
    `Q²·R` route this doc first sketched).
  * **§4 engines landed** — `cube_dvd_lcm_cube : j³ ∣ lcm(1..n)³` (`1≤j≤n`, harmonic
    part) and `heart_lcm : m³·C(n,m)·C(n+m,m) ∣ lcm(1..n)³·C(n,k)·C(n+k,k)` (`1≤m`,
    Heart at `d=lcm(1..n)` via KeyDiv + `lcmUpTo` monotonicity).

**§4 reduced-presentation inputs landed** (`FactorialLcmDvd.lean`, 11 PURE):
`dvd_factorial` (`k∣n!`), `lcmUpTo_dvd_factorial` (`lcm∣n!`), and
**`two_lcmCube_dvd_factCube`** (`2·lcm(1..n)³ ∣ (n!)³` for `n≥4`) — so the common
factor `c n = (n!)³/(2·lcm³)` is an integer for `n≥4`.  The `2` comes from `2` and
`2^{⌊log₂n⌋}` being distinct factors `≤ n` (`mul_dvd_factorial`) ⟹ `v₂(n!)≥
v₂(lcm)+1` (`v2_fact_gt_lcm`).  Helpers: `prime2`, `vp_pow3`, `vp_two_two`,
`vp_two_eq_zero`, `vp_two_lcmUpTo`, `le_of_dvd_pos`.

### ★ THE NUCLEUS (what every route reduces to)

The consumer `zeta3_reduced_conditional` needs `zeta3Den n = c n · q n`, i.e.
**`(n!)³ ∣ zeta3Den n`** (then `q n = zeta3Den n/c n = 2lcm³·Bₙ`, `Bₙ = zeta3Den
n/(n!)³`).  By the cleared recurrence `x_{m+2} = aperyLead m·x_{m+1} −
(m+1)⁶·x_m` (`aperyBot m = (m+1)³`), with `((m+1)!)³ = (m+1)³(m!)³`, this reduces
**exactly** to the congruence

> **`(m+2)³ ∣ aperyLead m · B_{m+1} − (m+1)³ · B_m`**  (subtraction exact).

This is **Apéry's recurrence for the binomial sums** `Bₙ = Σ_k C(n,k)²C(n+k,k)²`
(equivalently: `(m!)³·Bₙ` satisfies the orbit recurrence) — the **WZ /
creative-telescoping identity**.  It is unavoidable: the recurrence alone does not
imply it; it is a special arithmetic property of these particular sequences.  Both
the "recurrence-divisibility" and "binomial-sum" routes collapse to this one
identity.  **This is the true remaining frontier nucleus** — a research-scale
∅-axiom WZ formalization.  Once it lands: `Bₙ`-integrality is immediate (sum form);
the numerator `Aₙ`-integrality uses the Brick-2 engines (`heart_lcm`,
`cube_dvd_lcm_cube`); then piecewise `(c,p,q)` (`n≤3` trivial, `n≥4` reduced) +
`htel` from `lcmUpTo_le` vs `zeta3Den_geom` (28>27) ⟹ `zeta3HolonomicReal`.

**Worked sub-frontier** → `zeta3_wz/` (Lean anchor `AperyRecurrence.lean`: `B(n)`
def + seeds + base-layer validation, PURE).  Verified there (CAS, reproducible):
the recurrence holds; the WZ combination `F(j,k)` sums to `0` (so a certificate
exists); the exact rational reduction
`R_F = −4(2j+3)·P₆(j,k)/[(j-k+1)²(j-k+2)²]` (`P₆` sextic).  Immediate next step:
extract the Gosper certificate (sympy `gosper_term` chokes on the binomials; the
GP obstruction is `P₆` at shift `h=j` → high-degree certificate).  See
`zeta3_wz/README.md`.

(Notes: `α₃₀` `[local irreducible]` to stop whnf-explosion; `ring_nat` deep-recurses
on literal-exponent `^` → abstract reassoc lemmas; base certificates `decide` with
`maxRecDepth`/`maxHeartbeats` raised — `lcmUpTo 750 ≤ 10^375` in ~1s.)

## Brick 1 — the lcm bound: finitized Chebyshev, NOT Hanson

**Deliverable**: `lcm(1..n)⁶ ≤ 10⁸⁷ · 1000ⁿ`, i.e. `lcm³ ≤ 10^{43.5}·(31.62)ⁿ`
with `c³ = 10^{1.5} = 31.62 < 33.97 = (1+√2)⁴` — 7.4%-per-`n` margin for the
Apéry certificate.  (Hanson `< 3ⁿ` REJECTED for formalization: its own margin
is < 0.5% (`max ln C_H(n)/n = 1.0942` at `n = 125` vs `ln 3 = 1.0986`) and the
Sylvester tail needs unbounded-`k` nested-exponent bookkeeping; ≈ 2× the cost.)

Chain (each step exhaustively verified, zero failures):
1. **Counting lemma** (`m̃ < 10⁵`): `[m̃≥1] + ⌊m̃/2⌋ + ⌊m̃/3⌋ + ⌊m̃/5⌋ ≤ m̃ +
   ⌊m̃/30⌋ + [m̃≥6]` — decide below 36, then exactly periodic (+31 per +30).
2. **Key divisibility** (`m ≤ 69`; general-`n` form to 600):
   `lcm(1..30m)·(15m)!(10m)!(6m)! ∣ (30m)!·m!·lcm(1..5m)` — per prime power
   `p^j`, bucket Legendre terms through lemma 1 at `m̃ = ⌊30m/p^j⌋`.
3. **Factorial-ratio bound** (`m ≤ 60`): `(30m)!·m!·6^{6m}15^{15m}10^{10m} ≤
   (6m+1)·(15m)!(10m)!(6m)!·30^{30m}` from three binomial-theorem term bounds
   (two single-term, one max-term with unimodality at `k = m`), with
   `α₃₀ := 30³⁰/(6⁶15¹⁵10¹⁰) = 2¹⁴3⁹5⁵ = 1 007 769 600 000` exact.
4. **Recursion** (`m ≤ 100`): `lcm(1..30m) ≤ (6m+1)·α₃₀^m·lcm(1..5m)`.
5. **Numeral induction**: `S(m): (6m+1)α₃₀^m W^{⌈m/6⌉} ≤ W^m` (`W = 10¹⁵`)
   holds ∀ `m ≥ 26`; the step is the single numeral `37·α₃₀⁶ ≤ 10⁷⁵`
   (25.8× slack); bases S(26..31) decide on ≤ 466-digit numerals.
6. **Main** (`m ≤ 69`): `lcm(1..30m) ≤ 10^{15m}` — strong induction; `m ≤ 25`
   by explicit lcm certificates (`k ∣ L_m` decide + `lcm_dvd` universal
   property + `Nat.ble`).
7. Corollaries by padding (`n ≤ 3000` verified): `lcm² ≤ 10^{n+29}`,
   `lcm⁶ ≤ 10^{87+3n}`.

Bonus exact structure found: **`lcm(1..2m) ∣ C(2m,m)·lcm(1..m)`** and
`lcm(1..2m+1) ∣ C(2m+1,m)·lcm(1..m+1)` (the lcm-doubling divisibilities,
exact, `m ≤ 400`) and `n! = Π_k lcm(1..⌊n/k⌋)`.

Cost ≈ 1000–1450 lines on existing repo infra (`Meta/Nat/Valuation.lean` vp,
`Lcm213.lean` universal property, `ChooseFactorial`, `BinomialTheorem` — all
present, all ∅-axiom).  Blocks: Legendre `v_p(n!)` (250–350), FTA-lite
(`∀ prime power q, q∣a → q∣b) → a∣b` (150–250), steps 1–2 (150–200), step 3
(250–350), steps 4–7 (200–300).

## Brick 2 — Apéry integrality: pure divisibility chains, NO p-adics

**Deliverable**: `2·lcm(1..n)³·aₙ ∈ ℤ`.  **No ord_p, no Kummer, no Legendre,
no primes** — the heart collapses to exact cofactor equations:

1. **Trinomial double identity** (exact, all triples):
   `C(n,k)C(n+k,k)·C(k,m)² = C(n,m)C(n+m,m)·C(n−m,k−m)·C(n+k,n+m)`.
2. **KeyDiv**: `m·C(k,m) ∣ lcm(1..k)` — witnessed ord_p-free by the
   finite-difference identity `Σ_{j≤s}(−1)ʲC(s,j)Π_{i≠j}(m+i) = s!`
   (induction on `s` via Pascal), giving the exact ℤ-equation
   `d_n = m·C(n,m)·Σ_{j≤n−m}(−1)ʲC(n−m,j)·(d_n/(m+j))` — every factor integer.
3. **Heart (L2)**: `m³C(n,m)C(n+m,m) ∣ d³·C(n,k)C(n+k,k)` — divide the double
   identity in; the remainder is `Q²·R·C(n−m,k−m)·C(n+k,n+m)` with
   `Q = d/(mC(k,m))`, `R = d/m` integers by KeyDiv.  One calc chain.
4. Assembly: termwise with the `C(n,k)²C(n+k,k)²` prefactor (the bare
   `2d³c_{n,k}` is NOT integral — fails at `(1,1)`, value `5/2`); the factor 2
   cancels the `2m³`; empirically `d³aₙ ∈ ℤ` even without the 2 (`n ≤ 60`).

Verified: 2925 triples `n ≤ 25` (heart, assembly), KeyDiv to `k = 50`
(re-verified here to 40), findiff to `s = 30`, recurrence cross-check to
`n = 60`.  Cost ≈ 1500–3000 lines; risk concentrated in findiff's `Π_{i≠j}`
reindexing (~300–400) and the ℚ-free assembly bookkeeping (~400–600).

## Assembly (after both bricks)

Reduced pair `Aₙ = 2lcm³aₙ`, `dₙ = 2lcm³bₙ`; `bₙ ≥ 28ⁿ`-type growth from the
Apéry recurrence (Zeta3Cut's growth invariant pattern); cross-det smallness
`12·lcm³·i² ≤ i³bₙ`-shape from Brick 1's `31.62ⁿ` vs `33.97ⁿ`;
`Htel_of_crossdet` + `rate_cut_const` ⟹ `zeta3CauchySeq` with total modulus
`k+2` — ζ(3) joins φ and e at the e-grade.

## Independent re-verification (this session)

Step-2 divisibility (m ≤ 28), step-3 inequality (m ≤ 24), `α₃₀` identity,
`37α₃₀⁶ ≤ 10⁷⁵`, Corollary 2 (n ≤ 900), KeyDiv (k ≤ 40), trinomial double
identity (n ≤ 15), heart L2 (n ≤ 15), findiff (s ≤ 15), T1-doubling
(m ≤ 199): **all pass, zero failures**.
