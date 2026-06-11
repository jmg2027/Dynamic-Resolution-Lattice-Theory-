# ζ(3) free modulus: the verified proof blueprint (both bricks)

**Status**: no open mathematics left — formalization plans only.  Produced by a
multi-agent derivation round; **every load-bearing claim independently
re-verified by exact integer computation** (ranges per item).  Companion to
`zeta3_free_modulus.md` (which states the problem and the clearing-growth
criterion forcing these two bricks).

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
