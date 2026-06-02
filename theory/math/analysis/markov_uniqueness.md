# The Markov uniqueness conjecture — the neighbor congruence and the `√(−1)` encoding

**Status**: The arithmetic spine of the conjecture is closed ∅-axiom; the conjecture itself is
verified decidably at small maxima and stated formally with its classical reduction held as an
explicit open target.  Source of truth (35 PURE / 0 dirty):
`lean/E213/Lib/Math/Real213/MarkovUniqueness.lean`.

## The conjecture

The Markov tree (`markov_spectrum.md`) labels each node with the maximum of its triple — the
Markov numbers `1, 2, 5, 13, 29, 34, 89, …`.  The **uniqueness conjecture** (Frobenius 1913)
states that this labeling is injective: each Markov number is the maximum of exactly one ordered
triple `(a, b, c)`, `a ≤ b ≤ c`.  It is one of the oldest open problems in Diophantine analysis.

## The neighbor congruence

The single equation `a² + b² + c² = 3abc`, reduced modulo the maximal entry `c`, gives the
arithmetic lever of every approach to the conjecture:

  `a² + b² ≡ 0 (mod c)`.

This is `markov_neighbor_dvd`: `c ∣ a² + b²`, with the explicit witness `a² + b² = c·(3ab − c)`.
The witness needs only `c ≤ 3ab` (`markov_le_3mul`), which itself follows because `c²` is one of
the three summands of `a² + b² + c² = 3abc`, so `c² ≤ 3abc` and one `c` cancels.  Everything is
pure `ℕ` arithmetic: the witness product `c·(3ab − c)` reconstructs the sum exactly, so the
truncated subtraction carries no obstruction.  By symmetry of the equation each entry divides the
sum of squares of the other two (`markov_neighbor_dvd_all`), and the residue form
`(a² + b²) % c = 0` (`markov_neighbor_residue`) records the same fact through the modulus.

## The square root of `−1`

When the second entry `b` is invertible modulo `c` — concretely `b·b' = 1 + c·j` for an inverse
`b'` and some `j` — the neighbor congruence upgrades to the statement that **`−1` is a quadratic
residue mod `c`**, witnessed by `u = a·b'`:

  `c ∣ (a·b')² + 1`     (`neg_one_qr_of_inverse`).

The proof multiplies `c ∣ a² + b²` by `b'²`, giving `c ∣ (a b')² + (b b')²`; since
`(b b')² = (1 + cj)² = 1 + c·M` with `M = 2j + c·j²`, this reads `c ∣ ((a b')² + 1) + c·M`, and
subtracting the multiple `c·M` leaves `c ∣ (a b')² + 1`.  The whole argument is additive except
one divisibility subtraction.  In `ℕ` there are no signs, and the `+1` on the left is exactly the
faithful encoding of `≡ −1`.

The encoding fires on the actual tree triples: mod `5` via `(1,2,5)` (`u = 3`, `3² + 1 = 10`),
mod `29` via `(2,5,29)` (`u = 12`, `12² + 1 = 145`), and mod `433` via `(5,29,433)`
(`u = 1120`).  These are `neg_one_qr_mod_{5,29,433}`.

## The reduction and where the difficulty lives

Distinct ordered triples sharing the same maximum `c` produce distinct `±u` roots of
`x² ≡ −1 (mod c)`.  Hence if that congruence has at most the two roots `±u`, the triple with
maximum `c` is unique.  The number of roots is `2^ω`, where `ω` counts the distinct odd prime
factors of `c` (each necessarily `≡ 1 mod 4`).  For a prime power `c = pᵏ` — and for `2pᵏ`,
`4pᵏ` — there are exactly two roots, so those Markov numbers are unique; this is the content of
the prime-power theorems.  The conjecture remains open precisely for composite `c` with two or
more distinct prime factors, where the root count is at least four.

Two definitions carry this in Lean.  `MarkovMaxUnique c` is the conjecture at a fixed maximum;
`SqrtNegOneTwoRoots c` is the root-count input (`x² ≡ −1 (mod c)` has at most the two roots
`±u`).  The reduction `SqrtNegOneTwoRoots c → MarkovMaxUnique c` is the spine of every partial
result, and its one non-elementary step — injectivity of the residue map
`triple ↦ a·b⁻¹ (mod c)` — is held as an explicit open target rather than asserted.

What is established directly: the conjecture itself at small maxima, `MarkovMaxUnique` for
`c = 5, 13, 29` (assembled from the decidable single-pair checks `markov_max_unique_{5,13,29,34}`);
the input `SqrtNegOneTwoRoots` for the prime powers `5, 13, 25` and the prime `29`; and the
boundary case `not_sqrtNegOneTwoRoots_65`, where `c = 65 = 5·13` already carries the four roots
`{8, 18, 47, 57}` and the pair `8, 18` breaks the two-roots input — the first place the open
difficulty appears.

## The `p ≡ 3 (mod 4)` obstruction

Because every prime factor of a Markov number admits a square root of `−1` through the neighbor
congruence, and `x² ≡ −1 (mod p)` is unsolvable when `p ≡ 3 (mod 4)`, no prime `≡ 3 (mod 4)`
divides a Markov number — every odd prime factor is `≡ 1 (mod 4)`.  The unsolvability is recorded
per prime in `no_sqrt_neg_one_mod_{3,7,11,19}`, against the solvable contrast at `5` and `13`.

## The Fibonacci spine: φ's convergents are the spine's `√(−1)` roots

The most native instance of the encoding is general and needs no inverse to exhibit.  The
Cassini/Catalan identity, already present as `golden_min_attained_on_fib` (the golden form
taking its minimum `−1` on φ's convergents), reads `fib(2n+2)² + 1 = fib(2n+1)·fib(2n+3)`.  So
the Fibonacci-spine Markov number `fib(2n+3)` divides `fib(2n+2)² + 1`:

  `fib(2n+3) ∣ fib(2n+2)² + 1`     (`fib_spine_sqrt_neg_one`, for every `n`),

i.e. `u = fib(2n+2)` is a square root of `−1` modulo `fib(2n+3)`.  The square root of `−1` that
indexes each Markov number on the golden spine is the *next Fibonacci convergent of* the
worst-approximable number φ — the convergent itself is the root, with no modular inversion
required.  The companion `fib_spine_sqrt_neg_one_pred` reads the same Cassini product on the
other factor (`fib(2n+1) ∣ fib(2n+2)² + 1`).  Concretely `fib(9) = 34 ∣ fib(8)² + 1 = 442 =
34·13`, and the root `21 = fib(8)` mod `34` is exactly the predicted convergent.

## Relation to the modular tower

The Markov coefficient is `NS = 3`, the trace of `P = [[2,1],[1,1]]`, and the tree is the
Stern-Brocot binary tree on `SL(2,ℤ)` data with the Fibonacci (golden, `√5`) and Pell (silver,
`√8`) spines.  The neighbor congruence identifies the second neighbor of a Markov number with a
square root of `−1` modulo the maximum — the same `i` carried by the order-4 elliptic generator
`S` of `PSL(2,ℤ) = ℤ₂ * ℤ₃` (`modular_generator_orders`).  The root that indexes a Markov number
and the Gaussian unit that fixes the order-4 cusp are one element.

This is made exact at the matrix level.  Each Markov number `c` carries a Cohn matrix
`C = [[a,b],[cc,d]] ∈ SL(2,ℤ)` (from its Stern-Brocot word in `A=[[2,1],[1,1]], B=[[5,2],[2,1]]`)
with `tr C = 3c` and `det C = 1`.  Cayley–Hamilton gives `C² = (tr C)·C − I = 3c·C − I`, so
`C² ≡ −I (mod c)`: reduced mod `c`, `C` is an order-4 element of `SL(2,ℤ/cℤ)` — a copy of the
Gaussian `i = S` carried along the tree path to `c`.  Because the entries are positive this is a
pure-`ℕ` statement (`cohn_sq_neg_one_mod`: from `a·d = b·cc+1` and `a+d = 3m`, each entry of `C²`
is congruent mod `m` to the entry of `−I`), instantiated at `cohn5_sq_neg_one_mod_5`
(`C=[[12,5],[7,3]]`, `C² = [[179,75],[105,44]] ≡ −I (mod 5)`).  So the defining relation of the
order-4 modular generator survives reduction mod every Markov number, along any tree path.

## How to verify

```bash
cd lean
lake build E213.Lib.Math.Real213.MarkovUniqueness
cd ..
python3 tools/scan_axioms.py E213.Lib.Math.Real213.MarkovUniqueness
```
Reports `35 pure / 0 dirty`.
