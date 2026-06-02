# G173 — Markov uniqueness conjecture: the ∅-axiom arithmetic spine + conjecture slate

**Tier 1 (volatile).**  Marathon working note for the Markov uniqueness conjecture
(Frobenius 1913), continuing the Markov arc (`theory/math/analysis/markov_spectrum.md`,
`Real213/{GoldenFormMarkov, MarkovTree}`).  Source of truth for the closed part:
`lean/E213/Lib/Math/Real213/MarkovUniqueness.lean` (28 PURE / 0 dirty).  Promoted narrative:
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

## What is closed ∅-axiom (`MarkovUniqueness.lean`, 28 PURE)

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

Reused infra: `Gcd213.{dvd_sub_213, dvd_add_213}`, `NatHelper.{mul_sub_distrib, mul_mod_right,
mul_mul_mul_comm_213}`.  The `%`-residue form (not `∣`) is used in `decide` statements — the
`Decidable (a ∣ b)` instance leaks `propext`, while `Nat.decidableBallLT` + `%`/`decEq` are pure.

## Conjecture / target slate (graded by ∅-axiom tractability)

Green = elementary/done; Yellow = formalizable but a tedious Nat-descent or moderate effort;
Red = needs imports far from the current arithmetic core, or depends on a Yellow/Red prerequisite.

- **C1 — neighbor congruence.**  `markovEq a b c → c ∣ a²+b²`.  **Proven** (`markov_neighbor_dvd`).  **Green ✓.**
- **C2 — single-pair coprimality.**  `gcd(b,c)=1` for the ordered max-element triple.  Classical; Lean: not yet.  **Green/Yellow** — descent on `c`; the minimal lemma actually needed to fire C4.  *Highest value/effort ratio — do next.*
- **C3 — full pairwise coprimality.**  `gcd(a,b)=gcd(b,c)=gcd(a,c)=1`.  **Yellow** — same descent ×3 + minimality.  Hurwitz "n∈{1,3}" NOT required (gcd-divides-all + minimal-solution descent suffices).
- **C4 — `u²≡−1` encoding.**  invertibility ⟹ `c∣(a·b')²+1`.  **Proven** (`neg_one_qr_of_inverse`).  **Green ✓** (gains full force once C2 lands).
- **C5 — prime-power root count.**  `x²≡−1 (mod pᵏ)` has exactly 2 roots if `p≡1 (mod 4)`, 0 if `p≡3 (mod 4)`.  The `p≡3` (0-root) branch is the clean win — order-4 / FLT argument; the repo HAS `universal_flt_main` (`a^(p−1)≡1 mod p`, ∅-axiom, per-prime gcd input).  The `p≡1` (existence) branch is **Yellow→Red** (constructing a root without `Classical`).  Finitary instances done (`no_sqrt_neg_one_mod_{3,7,11,19}`).
- **C6 — root-count ⇒ uniqueness reduction.**  `SqrtNegOneTwoRoots c → MarkovMaxUnique c`.  The *implication* is classical; the crux is **injectivity of the residue map** `triple ↦ a·b⁻¹ (mod c)` — recovering `(a,b)` from `u` via the Markov equation + size bounds.  **Yellow/Red.**  Formalizable but multi-week; a sloppy version risks asserting injectivity by fiat / going vacuous.  **Stated as an explicit OPEN target — never claimed.**
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

## Next

1. **C2** (single-pair `gcd(b,c)=1`) — the next ∅-axiom deliverable; Nat-descent on `c` using
   `markov_le_3mul` + `Gcd213`.  Unlocks unconditional firing of C4.
2. **C5 `p≡3` branch, general** — via `universal_flt_main`: `x²≡−1 ⟹ x^(p−1)≡(−1)^((p−1)/2)≡−1`
   contradicts FLT `≡1` for `p≡3 (mod 4)`.  Moderate; needs the per-prime gcd hypothesis route
   generalised or applied per prime.
3. **C6** — keep as a single named open Lean target; attempt only the residue-injectivity lemma
   in isolation, guarding against vacuity.
