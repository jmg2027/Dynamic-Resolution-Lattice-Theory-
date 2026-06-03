# G173 — Markov uniqueness conjecture: the ∅-axiom arithmetic spine + conjecture slate

**Tier 1 (volatile).**  Marathon working note for the Markov uniqueness conjecture
(Frobenius 1913), continuing the Markov arc (`theory/math/analysis/markov_spectrum.md`,
`Real213/{GoldenFormMarkov, MarkovTree}`).  Source of truth for the closed part:
`lean/E213/Lib/Math/Real213/MarkovUniqueness.lean` (80 PURE / 0 dirty).  Promoted narrative:
`theory/math/analysis/markov_uniqueness.md`.

## The conjecture

Markov triples = positive solutions of `x²+y²+z² = 3xyz`; Markov numbers = the maxima
`1,2,5,13,29,34,89,169,194,233,433,610,985,…`.  **Uniqueness conjecture** (Frobenius 1913):
each Markov number is the maximum of a *unique* ordered triple `(a,b,c)`, `a≤b≤c`.  Equivalently
the labeling of the Markov tree by its maximal element is **injective**.  **Open** >110 years;
"proofs have been claimed but none seems correct."

## The arithmetic spine (what makes it tractable)

Reducing `a²+b²+c² = 3abc` mod the maximum `c`:

  `a² + b² ≡ 0 (mod c)`     (the **neighbor congruence**).

If `gcd(b,c)=1`, set `u ≡ a·b⁻¹`: then `u² ≡ −1 (mod c)`.  So **every** triple with max `c`
produces a square root of `−1` mod `c`.  The load-bearing reduction: distinct ordered triples
sharing max `c` give **distinct** `±u` roots; hence

  **`#{x : x²≡−1 (mod c)} ≤ 2  ⟹  c is unique`.**

The root count is `2^(ω)` (ω = number of distinct odd prime factors of `c`, all `≡1 mod 4`).
So prime-power `c = pᵏ` (and `2pᵏ, 4pᵏ`) give exactly 2 roots ⟹ unique (Schmutz 1996, Button
1998/2001, Lang–Tan 2005, Zhang 2006).  The **open zone is exactly composite `c` with ≥2
distinct prime factors** (≥4 roots), where root-counting no longer forces a unique triple.

## What is closed ∅-axiom (`MarkovUniqueness.lean`, 80 PURE)

| theorem | content |
|---|---|
| `markov_le_3mul` | every entry `≤ 3·(product of the other two)` — gives `c ≤ 3ab` |
| `markov_neighbor_dvd` | **`c ∣ a²+b²`**, witness `a²+b² = c·(3ab−c)` — the neighbor congruence |
| `markov_neighbor_dvd_all`, `_residue` | the 3 symmetric forms + `(a²+b²)%c = 0` |
| `neg_one_qr_of_inverse` | **`b·b' = 1+c·j ⟹ c ∣ (a·b')²+1`** — the `u²≡−1` encoding |
| `neg_one_qr_mod_{5,29,433}` | the encoding fired on `(1,2,5),(2,5,29),(5,29,433)` |
| `markov_max_unique_{5,13,29,34}`, `markovMaxUnique_{5,13,29}` | conjecture verified decidably at small maxima |
| `no_sqrt_neg_one_mod_{3,7,11,19}` | `−1` a non-residue mod `p≡3 (mod 4)` |
| `MarkovMaxUnique`, `SqrtNegOneTwoRoots` | the conjecture + its root-count input, formalised |
| `not_sqrtNegOneTwoRoots_65` | `c=65=5·13` has 4 roots `{8,18,47,57}` — the obstruction onset |
| `markov_common_dvd_sq`, `markov_gcd_dvd_sq` | `d∣b → d∣c → d∣a²`; `gcd(b,c)∣a²` (coprimality foothold) |
| `markov_partner_is_triple` | the explicit Vieta partner `markovEq a b (3ab−c)` (tree edge map) |
| `fib_spine_sqrt_neg_one` (+`_pred`) | **`fib(2n+3) ∣ fib(2n+2)²+1`** ∀n, from Cassini — φ's convergents are the spine's `√(−1)` roots |
| `fib_spine_recurrence`, `pell_spine_recurrence` | **trace-`NS`/silver linear recurrences** of the Markov spines (`x²−3x+1`, `x²−6x+1`) — C-finite, the Vieta jump; Casoratian = Cassini = `√(−1)` residue (see `G174`) |
| `cohn_sq_neg_one_mod` (+`cohn5_…`) | **`C² ≡ −I (mod c)`** for `tr C = 3c`, `det C = 1` (Cayley–Hamilton) — the Cohn matrix is order-4 mod `c`, a copy of the Gaussian `i = S` |
| `coprime_vieta_step` | `gcd(a,c)=1 ∧ c+c'=3ab ⟹ gcd(a,c')=1` — the Vieta step preserves coprimality |
| `MarkovReachable`, `markov_reachable_coprime` | **every tree triple is pairwise coprime** (C3, induction on the tree); `markov_reachable_is_triple` (sound: reachable ⟹ markovEq), `markov_reachable_gcd_bc` (C2) |
| `neg_one_qr_of_mod` | the encoding from a modular inverse in residue form `(b·b')%c = 1` (Bezout-ready) |
| `MarkovPrimeFactor.no_sqrt_neg_one_4k3` | **general `p≡3(mod4) ⟹ ¬(p∣x²+1)`** via FLT (separate file `ModArith/MarkovPrimeFactor`, 28 PURE) — no prime `≡3(4)` divides a Markov number |
| `MarkovPrimeFactor.euclid_via_inverse` | **Euclid's lemma** `(a·a')%p=1 ∧ p∣a·b ⟹ p∣b`, constructively from the modular inverse |
| `MarkovPrimeFactor.two_roots_of_prime` | **`SqrtNegOneTwoRoots p` for every prime `p`** — `x²≡−1` has ≤2 roots mod a prime (the C6 input at prime maxima), GENERAL not `decide` |
| `MarkovPrimeFactor.inverse_of_coprime` | **`gcd213 a m = 1 ⟹ ∃ inverse`** — xgcd correctness (`xgcdAux_dvd_both` under bound `fuel≥r₁+1`); closes C2→C4 |
| `markov_reachable_neg_one_qr` | **unconditional `√(−1)` on every reachable triple** (`1<c`): `c ∣ (a·b⁻¹)²+1`, no invertibility hypothesis (from the tree's coprimality) |
| `vieta_reflection` | the Vieta jump `c↦3ab−c` as a **difference reflection** (`c+c'=3ab`) + involution — the ℤ-difference-Lens reading; annihilator `Δ²−Δ−1` (golden), strictly C-finite not poly-depth (see `G174`) |
| `sqrtNegOneTwoRoots_prime_pow` | **`SqrtNegOneTwoRoots (p^(k+1))`** promoted to the named predicate for every odd prime power (Button/Zhang `≤2` roots) |
| `markov_phantom_root_filter` | **phantom-root filter at `c=65=5·13`** (C6 sniper): the `2^ω=4` root explosion `{8,18,47,57}` over-counts, yet `markovEq · · 65` admits no triple — all roots phantom (the descent constraint is the separating observer) |
| `markov_recovery` | **the recovery map** `a = (u·b) mod c` (`u = a·b⁻¹`) — backbone of the per-`c` uniqueness certificate (2-D→1-D reduction); engine the phantom filter runs on |
| `markov_composite_separation` | **first real-composite separation** at `c=1325=5²·53` (4-root Markov number): `markovEq` separates the 4 roots `{182,507,818,1143}` into the valid pair `{507,818}` (recovers triple `(13,34,1325)` via `a=(u·b)%c`) and the phantom pair `{182,1143}` (`∀b ¬markovEq`) |
| `markov_root_recovery` | **the 2-D→1-D bundle**: a triple `(a,b,c)`, `gcd(b,c)=1`, gives a root `u=(a·b⁻¹)%c` of `x²≡−1` *and* `a=(u·b)%c`.  Pins a triple by `(u,b)`, `u` in the finite root set — uniqueness is a per-root 1-D search over `b` |
| `markov_descent_ineq` (§2b) | **`a²+2b² ≤ 3ab²`** for `1≤a≤b` (= `f(b)≤0` for the Vieta quadratic `f(t)=t²−3ab·t+(a²+b²)`) — the descent engine |
| `markov_vieta_partner_le`, `markov_partner_lt_max` | **`c'=3ab−c ≤ b < c`** for `1≤a≤b`, `b<c` — the down-move drops the max (descent ineq in product form `c·c'+b² ≤ b·c+b·c'`, gap `(d+1)(e+1)>0`) |
| `markov_mid_lt_max` | **`b < c`** for any triple with `c≥2` (the max is strict; `b=c` only at `(1,1,1)`) |
| ★★ `markov_ordered_reachable` (§10b) | **Markov's descent theorem**: every ordered triple is reachable from `(1,1,1)` — `reachable_of_fuel` structural recursion on a fuel ≥ max (∅-axiom, no `WellFounded.fix`); `c≥2` descends to `{a,b,3ab−c}` (max `=b<c`) |
| ★★ `markov_ordered_coprime` | **pairwise coprimality for EVERY triple** (not just the tree) = descent ∘ `markov_reachable_coprime`.  The primitivity of Markov triples |
| `markov_hcop_general` | the `hcop` input (`gcd(b,c)=1`) for ALL `c≥2` at once — `a≥1` forced by the equation |
| ★★ `markov_max_unique_of_4roots` | **general per-`c` uniqueness from a 4-root certificate**: root-set disjunction `{r₁..r₄}` + four decidable per-root certs ⟹ `MarkovMaxUnique c` (coprimality/`a≥1`/`b<c` discharged internally via descent + recovery).  Each new 4-root composite is a one-liner |
| `markov_a_pos` | `a ≥ 1` for any Markov triple with `c ≥ 2` (`a=0` forces `c=0`) |
| ★ `markov_max_unique_1325`, `_985`, `_610` | **UNCONDITIONAL** uniqueness at three 4-root composites: `1325=5²·53` `(13,34)`, `985=5·197` `(2,169)`, **`610=2·5·61` `(1,233)` — the first EVEN composite**.  Each a one-liner via `markov_max_unique_of_4roots`, all ∅-axiom |
| `markov_max_unique_of_2roots` | the **2-root (prime / prime-power) class**, packaged like `of_4roots` with two certs (`c = pᵏ,2pᵏ,4pᵏ` have roots `{r,c−r}`) |
| ★ `markov_max_unique_169`, `_233`, `_433` | **UNCONDITIONAL** Button/Zhang class: `169=13²` `(2,29)` — **first prime-power composite**; `233` (prime) `(1,89)` roots `{89,144}` consecutive Fibonacci; `433` (prime) `(5,29)` |
| ★★ `markov_max_unique_{2,89,194}`, `markovMaxUnique_34` | **COMPLETE the small range** — with the above, *every* Markov number `2 ≤ c ≤ 1325` is verified unique, ∅-axiom: `{2,5,13,29,34,89,169,194,233,433,610,985,1325}`.  (The in-kernel `decide` over `b<c` C-stack-overflows for `c≳1500`; beyond needs the general residue-map injectivity, not enumeration) |
| `markov_reachable_no_3mod4_factor` | **no prime `≡3(mod4)` divides a reachable Markov number** (Zhang 2007) — joins the two files: `√(−1)` exists mod `c` (`markov_reachable_neg_one_qr`) but not mod a `p≡3` factor (`no_sqrt_neg_one_4k3`) |
| `MarkovPrimeFactor.euclid_of_coprime` | **fully general Euclid's lemma**: `gcd213 a m = 1 ∧ m∣a·b ⟹ m∣b` (any `m>1`) |
| `MarkovPrimeFactor.coprime_prime_pow` | `p∤n ⟹ gcd213 n (pᵏ) = 1` (`dvd_prime_pow_cases`: divisors of `pᵏ` are `1` or `p·…`) |
| `MarkovPrimeFactor.two_roots_of_prime_pow` | **`SqrtNegOneTwoRoots (p^(k+1))` for odd prime `p`** — `x²≡−1` has ≤2 roots mod a prime power (the Button/Zhang case): `p` divides at most one of `x±y`, the coprime one cancels |

Reused infra: `Gcd213.{dvd_sub_213, dvd_add_213}`, `NatHelper.{mul_sub_distrib, mul_mod_right,
mul_mul_mul_comm_213}`.  The `%`-residue form (not `∣`) is used in `decide` statements — the
`Decidable (a ∣ b)` instance leaks `propext`, while `Nat.decidableBallLT` + `%`/`decEq` are pure.

## Conjecture / target slate (graded by ∅-axiom tractability)

Green = elementary/done; Yellow = formalizable but a tedious Nat-descent or moderate effort;
Red = needs imports far from the current arithmetic core, or depends on a Yellow/Red prerequisite.

- **C1 — neighbor congruence.**  `markovEq a b c → c ∣ a²+b²`.  **Proven** (`markov_neighbor_dvd`).  **Green ✓.**
- **C2 — single-pair coprimality.**  `gcd(b,c)=1`.  **Proven along the tree** (`markov_reachable_gcd_bc`) — the input C4 needs, now structural.  **Green ✓.**
- **C3 — full pairwise coprimality.**  `gcd(a,b)=gcd(b,c)=gcd(a,c)=1`.  **Proven along the tree** (`markov_reachable_coprime`): the *invariant* of the Vieta generation (`coprime_vieta_step` preserves it under a jump, transpositions permute it), over the inductive `MarkovReachable` predicate (sound: `markov_reachable_is_triple`).  No descent / no Hurwitz needed — preservation + induction.  **Green ✓.**  (Gap to *all* Markov triples = "every triple is reachable", Markov's theorem, which is the descent.)
- **C4 — `u²≡−1` encoding.**  invertibility ⟹ `c∣(a·b')²+1`.  **Proven** (`neg_one_qr_of_inverse`).  **Green ✓** (gains full force once C2 lands).
- **C5 — prime-power root count.**  `x²≡−1 (mod pᵏ)` has exactly 2 roots if `p≡1 (mod 4)`, 0 if `p≡3 (mod 4)`.  Both the **`p≡3` (0-root) branch** (`no_sqrt_neg_one_4k3`, via FLT) **and the `≤2` direction for ALL odd prime powers** (`two_roots_of_prime_pow`: `SqrtNegOneTwoRoots (p^(k+1))` — `p` divides ≤1 of `x±y`, the coprime one cancels via `euclid_of_coprime`) are **Green ✓**.  Only the `p≡1` *existence* (`≥1` root, Wilson) is **Yellow→Red** (no `Classical`).
- **C6 — root-count ⇒ uniqueness reduction.**  `SqrtNegOneTwoRoots c → MarkovMaxUnique c`.  The **input `SqrtNegOneTwoRoots` is now PROVEN for every prime `p` AND every odd prime power `p^(k+1)`** (`two_roots_of_prime`, `two_roots_of_prime_pow`) — so the reduction's hypothesis is discharged at every prime-power maximum (the full Button/Zhang `pᵏ` class).  The reduction *itself* (the implication) is the open part: the crux is **injectivity of the residue map** `triple ↦ a·b⁻¹ (mod c)` — recovering `(a,b)` from `u`.  **Yellow/Red.**  A sloppy version risks asserting injectivity by fiat / going vacuous.  **Stated as an explicit OPEN target — never claimed.**
- **C7 — prime-power Markov numbers are unique** (Baragar/Button/Zhang).  = C5 ∘ C6.  **Red** (aspirational capstone; depends on the hard reduction).
- **C8 — Aigner monotonicity** (fixed numerator / denominator / sum).  **Proven** — Rabideau–Schiffler 2020 (numerator, denominator), Lagisquet–Pelantová–Tavenas–Vuillon 2020 (sum).  Necessary conditions, *not* equivalent to uniqueness.  **Red** for ∅-axiom (continued-fraction / Christoffel-word combinatorics; huge import surface).

## Discussion record (red-team synthesis)

- **Non-triviality of C4.** Hypothesis `b·b'=1+c·j` is invertibility, not vacuous; conclusion
  `c∣(a·b')²+1` is the genuine `−1`-QR statement (the `+1` Nat phrasing *is* `≡−1`, lossless).
  Verified concretely: `(1,2,5)→u=3, 3²+1=10=5·2`; `(2,5,29)→u=12, 12²+1=145=29·5`;
  `(5,29,433)→u=1120, 433∣1120²+1`.
- **Devil's advocate.** C1/C4 are one-line classical reductions (Frobenius ~1913); the open
  difficulty lives entirely in C6's residue-injectivity-at-composite-`c` and the root blow-up
  for ≥2 prime factors — exactly the Red/Yellow steps the arc does not yet close.  So one could
  call this "axiom-free certificates on the easy direction."
- **Rebuttal.** The value is (i) a machine-checked, axiom-free *spine of the whole reduction
  chain*; (ii) C2's constructive Nat-descent coprimality is a reusable artifact (no Classical,
  no Mathlib); (iii) naming C6's injectivity as a single precise Lean target converts "uniqueness
  is hard" into a falsifiable lemma — where formalization adds rigor the literature is loose
  about.  External enumeration confirms all 2049 Markov numbers below `~10⁹` are unique
  (consistent with the conjecture; no counterexample known).

## 213-native angle

The Markov coefficient is `NS = 3` (`markov_coefficient_is_NS`), the trace of `P=[[2,1],[1,1]]`.
The tree is the Stern-Brocot binary tree on `SL(2,ℤ)` data (`Mobius213SternBrocot`); its two
spines are the repo's Fibonacci (golden, `√5`) and Pell (silver, `√8`) recurrences.  The
neighbor congruence `c ∣ a²+b²` says the second neighbor is a `√(−1)` mod the max — and
`PSL(2,ℤ)=ℤ₂*ℤ₃` (`ModularElliptic`) carries the elliptic order-4 element `S` (the Gaussian
`i = √(−1)`).  So the `√(−1)`-root that indexes a Markov number is the same `i` as the order-4
modular generator.  Possible 213-native conjecture: the Markov-number ↦ `√(−1)`-residue map is
the Stern-Brocot ↦ `PSL(2,ℤ)`-elliptic correspondence restricted to the `c=2` `K_{3,2}` axis —
to be sharpened.

**Closed this session (the Fibonacci spine, general ∀n):** `fib_spine_sqrt_neg_one` —
`fib(2n+3) ∣ fib(2n+2)²+1`, straight from the repo's Cassini identity
`golden_min_attained_on_fib` (`fib(2n+2)²+1 = fib(2n+1)·fib(2n+3)`).  So along the golden spine
the `√(−1)` residue of the Markov number `fib(2n+3)` is `u = fib(2n+2)` — *φ's next convergent*.
The worst-approximable number's convergents are exactly the `√(−1)` roots indexing its Markov
spine; no modular inversion is needed (the convergent IS the root, by Cassini).  E.g.
`fib9=34 ∣ fib8²+1 = 442 = 34·13`, root `21=fib8` mod `34`.  This is the cleanest 213-native
realisation of the encoding: the Markov spine, the golden form's `−1`-minimum, and the `√(−1)`
root all coincide on the Fibonacci convergents.

## Injectivity analysis (`Real213/MarkovInjectivity`, marathon + literature deep-dive)

A literature deep-dive (Zhang 2007 `math/0606283`; Lang–Tan `math/0508443`; Baragar 1996; Button
1998; Aigner's book) **recalibrated** the open locus.  The classical reduction is:

> `MarkovMaxUnique c  ⟸  SqrtNegOneTwoRoots c` (root-count ≤ 2)  `∧  residue-map injective`.

What this session pinned down:

- **The triple ↦ root map is the EASY direction** (Zhang Lemma 2: `u_t/m_t` strictly monotone in
  the Farey slope `t`, so the root + `c` recovers the ordered triple).  The **open** content is
  *root-counting*: for composite `c` with `ω ≥ 2` distinct prime factors, `x²≡−1 (mod c)` has
  `2^{ω−1}` window-roots and it is unknown that ≤ 1 is *Markov-realisable*.  (Our per-`c` `decide`
  certificates do exactly this counting, ≤ 1325.)
- **Zhang Lemma 4 — DONE** (`root_unique_below_half`): with `SqrtNegOneTwoRoots c`, `x²≡−1` has
  **≤ 1 root in `(0,c/2)`** (the `x+y=c` alternative is impossible when `2x,2y<c`).  General,
  ∅-axiom; the prime-power instance `root_unique_below_half_prime_pow` uses primality *only* through
  `sqrtNegOneTwoRoots_prime_pow`.  This is the single place primality enters Button's theorem.
- **Dead end recorded** (`coprime_cross_eq` + `markov_same_root_parallel`): same-root triples are
  parallel mod `c` (`c ∣ a₁b₂−a₂b₁`, proven), and coprime+*exact*-parallel ⟹ equal (proven), BUT
  the tempting finish `|a₁b₂−a₂b₁| < c` is **FALSE** — by Frobenius's identities
  `u_t·m_r − u_r·m_t = m_s` the cross-determinant equals a *neighbour Markov number* (≈ `c`), a
  genuine nonzero multiple of `c`.  No determinant size bound closes it.
- **Capstone reduction — DONE** (`markov_max_unique_of_same_pair_injective`): `MarkovMaxUnique c ⟸
  SqrtNegOneTwoRoots c ∧ SamePairInjective c`, the exact Frobenius/Aigner reduction (both inputs
  honest, neither is `MarkovMaxUnique` in disguise).  `markov_prime_pow_unique_of_same_pair_injective`:
  for `c=p^(k+1)`, uniqueness ⟸ `SamePairInjective` ALONE — **Button's prime-power unicity (infinite
  family) is reduced to the single residue-injectivity input** `SamePairInjective` (= Zhang Lemma 2).
- **Remaining for prime-power uniqueness (Button) as an infinite family**: only `SamePairInjective`
  = the **Farey-monotone recovery** (Zhang Lemma 2).  Realized **on the Fibonacci spine**
  (`MarkovCassiniBridge.spine_residue_farey`: `fib(2n+1)·fib(2n+2)=fib(2n)·fib(2n+3)+1`, the
  `(residue,max)` pairs are unimodular Farey neighbors).  Generalising to all `c` needs the
  continued-fraction / Stern-Brocot recovery (repo: `Mobius213SternBrocot`,
  `Cohomology/BipartiteStermBrocotClassification`, `Mobius213/Px/ConvergentDet` Farey det = 1).

## Next

1. **C2→C4 inverse-existence bridge** — **DONE** (`inverse_of_coprime` via `xgcdAux_dvd_both`).
   The encoding now fires unconditionally on every reachable triple (`markov_reachable_neg_one_qr`).
2. **C5 `p≡1` branch** — *existence* of a root of `x²≡−1 (mod pᵏ)` for `p≡1(mod4)` (the
   `p≡3` no-root branch is now done, `no_sqrt_neg_one_4k3`).  Existence without `Classical` is
   the hard part (Wilson `((p−1)/2)!` construction / explicit search bound).
3. **C6 residue-injectivity** — the one open crux now that `SqrtNegOneTwoRoots p` (prime) is
   done: prove `triple ↦ a·b⁻¹ (mod c)` injective on ordered triples with max `c` (recover
   `(a,b)` from the root `u` + size bounds + the Markov equation).  Attempt in isolation,
   guarding against vacuity.  Closing it would give prime-Markov-number uniqueness (C7) outright.

## Main-content synthesis (2026-06 re-merge: Cassini / orbit / modular threads)

Re-merging `origin/main` brought the **Cassini-unimodular / orbit-depth** thread
(`CassiniUnimodular`, `CassiniDepthFloor`, `SecondCasoratian`, `FibCassiniNat`), the
**`UnitsToModular`** bridge (`ℤ[i]^× → M₂(ℤ)` regular rep, `repI i = S`), and the **`ring_intZ`**
ℤ-reflection tactic.  These illuminate the Markov work:

- **The √(−1)-residue IS a Casoratian/Cassini value (now a theorem).**  `CassiniUnimodular`'s
  `det_closed` says a 2nd-order `Int` orbit's Cassini `D(n)=qⁿ·D(0)` is governed by the shift's
  multiplier `q`.  The Markov–Fibonacci spine carries both unimodular readings:
  `q=−1` (standard Cassini, alternating) gives the √(−1) — `fib(2n+2)²+1 = fib(2n+1)·fib(2n+3)`
  (= `fib_cassini_norm`), so `fib(2n+3) ∣ fib(2n+2)²+1`; `q=+1` (index-gap-2, conserved) gives the
  unit — `fib(2n+1)·fib(2n+5) = fib(2n+3)²+1`.  Both ∅-axiom in `Real213/MarkovCassiniBridge`
  (`markov_spine_{sqrt_neg_one_cassini, fib_second_cassini, cassini_dichotomy}`).  This grounds
  G174's "Casoratian = Cassini = √(−1)" as Lean, and places the Markov spine on the depth-0
  Cassini floor (`CassiniDepthFloor`).

- **The √(−1)-residue = the Gaussian unit `i` = `S`, reduced mod `c`** — now **Lean**
  (`Real213/MarkovModularBridge`, 2 PURE).  `UnitsToModular.repI i = S` (`S = [[0,-1],[1,0]]`,
  order 4, `S²=−I`).  `markov_pair_eigen`: for a Markov triple the residue `u=(a·b⁻¹)%c` satisfies
  `(u·b)%c=a` (recovery) and `(u·a+b)%c=0` (neighbor congruence `a²+b²≡0` + Euclid) — these ARE
  `S·(a,b)≡u·(a,b) (mod c)` (since `S·(a,b)=(−b,a)`).  `S_eigenvector_of_dvd` (ℤ, `ring_intZ`) is
  the abstract criterion consuming exactly those two divisibilities.  So the Markov **pair `(a,b)`
  is `S`'s eigenvector** mod `c` with eigenvalue the √(−1)-residue — the Cohn matrix
  (`cohn_sq_neg_one_mod`, `tr=3c,det=1,C²≡−I`) is the Markov-tree image of `S = `Gaussian-`i` mod
  `c`.  This realizes the HANDOFF "213-native conjecture" (Markov↦√(−1) = Stern-Brocot↦`PSL₂(ℤ)`-
  elliptic).  (Honest: the eigenvector content is recovery + neighbor congruence; the `S`-framing
  is the structure-map reading, per `UnitsToModular`'s own construction-tautology caveat.)

- **`ring_intZ` for the open injectivity (C6).**  The residue-map injectivity argument is
  cleanest over `ℤ` (the quadratic `f(b)=(b−c)(b−c')`, the Vieta sign reasoning I did awkwardly in
  `ℕ` for `markov_vieta_partner_le`).  `ring_intZ` (multivariate `Int` reflection) is the tool if
  C6 is attempted — work the descent/injectivity over `ℤ` then cast.
