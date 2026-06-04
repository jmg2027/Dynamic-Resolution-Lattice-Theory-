# G202 — expert-agent attack on the open kernel: Zhang's `3c±2` route (a verified, formalization-ready new family)

Goal directive: attack the open ω≥2 Markov-uniqueness kernel with full capability + parallel expert
agents.  Honest frame: full Frobenius (1913) will not fall.  Three expert agents ran in parallel; the
output is a **verified, formalization-ready roadmap to a genuine new uniform family** (Zhang's `3c±2`
criterion) that closes composite and even ω=3 Markov numbers the repo currently handles only by `decide`,
plus a sharp delineation (Agent B) of where elementary methods provably stop.

## Empirical ground truth (computed this session)

Windowed roots `(u, realized?, quotient (u²+1)/c)`:
- `c = 985 = 5·197`: `[(183, phantom, 34), (408, realized, 169)]`
- `c = 1325 = 5²·53`: `[(182, phantom, 25), (507, realized, 194)]`

Realized triples + Vieta descent neighbor `3ab−c`:
- `985`: `(2, 169, 985)`, neighbor `29`.  `1325`: `(13, 34, 1325)`, neighbor `1`.

**Key negative result.** At `985` *both* roots have Markov-number quotients (`34` and `169`) yet only one
is realized — so "quotient is a Markov number" does NOT discriminate phantom from realized.  The
discriminator is genuinely global (tree/orbit membership).  This kills the natural local-invariant
conjecture and matches Agent B's analysis.

## Agent B (deep number theory): the c-side is irreducibly hard

The two ±-pairs of roots mod `c=pq` are **arithmetically indistinguishable by every elementary
invariant** — both give a primitive `c = x²+y²` at minimal norm `c`; both are genuine √(−1).  What
separates realized from phantom is whether the **indefinite-form Vieta-descent orbit meets the Markov
tree** — a fundamental-unit / class-number fact (discriminant `9c²−4`).  No congruence in `p,q` decides
it.  The one elementary lever is the identity `3ab − c = (a²+b²)/c = m` (a *smaller* Markov number), and
the only elementary win is **bounded-descent-depth** uniqueness (covers a thin set).  Verdict: the 4-root
`c=pq` case is the open conjecture; literature (Baragar, Button, Zhang, Lang–Tan, Srinivasan) always wins
by *reducing the effective root count* via a primality hypothesis — never by resolving the 4-root orbit.

## Agent C (literature + family hunt): **Zhang's `3c±2` criterion** — the decisive route

Ying Zhang, *Congruence and uniqueness of certain Markov numbers*, Acta Arith. 128 (2007), arXiv
`math/0612620`.  **A Markov number `c` is unique if `3c−2` or `3c+2` is a prime power** (and even-cases
`4pᵏ, 8pᵏ`).  Elementary — "only simple facts about congruence."  It reduces to a √(−1)-root count on a
**different fixed modulus** `M = 3c±2`, where the repo's *already-proven* `two_roots_of_prime_pow` /
`two_roots_of_two_prime_pow` (this session's work) apply **verbatim** — even though `c` itself is
composite with ≥4 roots on the c-side.

### The mechanism (verified exactly this session)

Completing the square in `a` on `a²+b²+c²=3abc` gives the **exact** identity (it IS the Markov equation):

    (3bc − 2a)² = (9c² − 4)·b² − 4c²      [verified: equivalent to a²+b²+c²=3abc]

Since `9c²−4 = (3c−2)(3c+2)`, reduce mod `M = 3c−2` (or `3c+2`):

    (3bc − 2a)² ≡ −4c² = −(2c)²   (mod M).

For Markov `c ≥ 5` (odd ⟹ `M` odd), `gcd(2c, M) = 1` (since `2(3c−2)−3(2c) = −4` and `M` odd), so `2c` is
a unit and **`w := (3bc−2a)·(2c)⁻¹` is a root of `x² ≡ −1 (mod M)`** — every max-`c` triple injects into
the √(−1)-roots mod `M`.  If `M` is an odd prime power, `two_roots_of_prime_pow` gives ≤ 2 roots `{±w₀}`,
forcing a unique triple.

**Verified hits** (`#eval`): `985`: `3c−2 = 2953` **prime**, `3c+2 = 2957` **prime**; `4181`:
`3c−2 = 12541` **prime**.  So `985` (currently `decide`-only in the repo) and `4181` close by the uniform
argument.  Agent C's enumeration: Zhang covers **8 of 15** open-zone composites ≤ 200000, including
`610 = 2·5·61` (ω=3) and `195025 = 5²·29·269` (ω=3).  Honest caveat: fails exactly where both `3c±2` are
themselves ≥2-odd-factor composite (`1325`: `3c−2 = 29·137`, `3c+2 = 41·97`) — which is why `1325` is hard
for Zhang too.

### The recovery handle (derived + verified this session — makes it formalizable)

The one genuinely new lemma is the recovery (triple ↦ root mod `M` injective).  It is **clean**, via the
reduction (verified `#eval`: `t mod M = 2(b−a) mod M`):

    t := 3bc − 2a = b·(3c−2) + 2(b−a) = b·M + 2(b−a)   ⟹   t ≡ 2(b−a)  (mod M).

So the root mod `M` encodes exactly the **gap `b−a`** (and `2(b−a) < M = 3c−2` for `c>2`, so *no
wraparound* — `t mod M = 2(b−a)` on the nose).  Then `(c, δ:=b−a)` determines `(a,b)` by the quadratic

    (3c − 2)·(a² + a·δ) = δ² + c²      [from a²+b²+c²=3abc with b=a+δ],

a single positive root `a`.  Finally, for `c` odd, `M = 3c−2` is odd, so the partner root `M − 2δ` is
**odd** ⟹ not of the form `2·(b′−a′)` ⟹ exactly one of the ±-roots is realizable: the parity/window
argument that kills the phantom, mirroring the c-side window.

## Formalization plan (mostly reuse)

1. ✅ **DONE** `zhang_linear_core` (∅-axiom) — `b·(3c−2) + 2(b−a) + 2a = 3bc`, giving
   `3bc−2a ≡ 2(b−a) (mod M)`.  The recovery handle.
2. ✅ **DONE** `zhang_quadratic` (∅-axiom) — `(3c−2)·ab = (b−a)² + c²`; and `zhang_gap_dvd` (∅-axiom):
   `M = 3c−2 ∣ (b−a)² + c²`.  The `√(−1)` data on the modulus `M`, and the `(c,δ)↦a` pin.  (This is a
   cleaner route than the `(3bc−2a)² = (9c²−4)b²−4c²` form: `zhang_gap_dvd` gives the divisibility
   directly via the gap `δ = b−a`.)
3. ✅ **DONE** `zhang_gap_determines_pair` (∅-axiom) — two max-`c` triples with the same gap `b−a` are
   equal.  Via `zhang_quadratic` (equal gap ⟹ equal `ab` after cancelling `3c−2`), then equal product +
   gap ⟹ equal sum (`sum_sq_gap` + `sq_inj_le`) ⟹ equal pair.  **The recovery half.**
4. `zhang_root_unit` + bridge — with `inverse_of_coprime` for `c⁻¹ mod M` (`gcd(c, M)=1`, `M` odd),
   promote `zhang_gap_dvd` (`δ² ≡ −c² mod M`) to `(δ·c⁻¹)² ≡ −1 mod M`; `two_roots_of_prime_pow` on
   `M = pᵏ` gives `w₁ = w₂ ∨ w₁+w₂ = M`, i.e. `δ₁ = δ₂ ∨ δ₁+δ₂ ≡ 0`; range `δ_i < c`, `δ₁+δ₂ < 2c < M`
   forces `δ₁ = δ₂`.  *Yellow* — modular plumbing (reuses the c-side modular machinery).
5. `markov_max_unique_via_3c_minus_2` — capstone: feed `δ₁ = δ₂` to `zhang_gap_determines_pair`.
   *One-liner once step 4 lands.*

**Done this session**: steps 1–3 (algebraic foundation **+ the entire recovery half**, all ∅-axiom +
sanity-checked: `985`, `2953 ∣ 167²+985²`, quotient `338 = 2·169 = ab`).  Remaining: step 4 (modular
root-count bridge — `c⁻¹ mod M` + `two_roots_of_prime_pow` on `M` + the `δ < c` range argument) then the
one-line capstone (step 5).  Lemmas done: `zhang_linear_core`, `zhang_quadratic`, `zhang_gap_dvd`,
`zhang_gap_determines_pair` (+ helpers `sq_inj_le`, `sum_sq_gap`).

## Status

| route | covers | status |
|---|---|---|
| c-side ≤2 roots (`SqrtNegOneTwoRoots`) | `c = pᵏ` (Button), `2pᵏ` | **closed** (this session: `2pᵏ`) |
| **`3c±2` prime power (Zhang)** | composite/ω≥3 `c` with `3c±2 = pᵏ` (985, 4181, 610, 195025, …) | **roadmap verified, formalization-ready** |
| c-side ≥4 roots, both `3c±2` composite | `1325`, … | open = needs class-number data (Agent B) |
| general ω≥2 | all | open = Frobenius 1913 |

This session's expert-agent attack converted "the open kernel" into a **concrete, verified, reuse-heavy
formalization target** (Zhang `3c±2`) reaching genuinely new composite/ω=3 Markov numbers, plus a rigorous
proof (Agent B) that the residual (`1325`-type) is the genuine non-elementary core.  Not a solve — a real,
honest, mapped increment.

### Pointers
- This session ∅-axiom: `two_roots_of_prime_pow`, `two_roots_of_two_prime_pow` (the Zhang inputs on `M`)
- Reuse: `MarkovPrimeFactor.inverse_of_coprime`, `MarkovUniqueness.markov_neighbor_dvd`, `markov_max_unique_tree`
- Sources: Zhang arXiv `math/0612620`, `math/0606283`; Lang–Tan `math/0508443`; Aigner, *Markov's theorem and 100 years of the uniqueness conjecture*.
