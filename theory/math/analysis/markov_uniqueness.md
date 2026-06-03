# The Markov uniqueness conjecture — the neighbor congruence and the `√(−1)` encoding

**Status**: The arithmetic spine of the conjecture is closed ∅-axiom; the conjecture itself is
verified decidably at small maxima and stated formally with its classical reduction held as an
explicit open target.  Source of truth (80 PURE / 0 dirty):
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

The root-count input itself is now proved **generally for primes**.  In
`ModArith/MarkovPrimeFactor`, `two_roots_of_prime` shows `SqrtNegOneTwoRoots p` for every prime
`p` (with the prime-gcd hypothesis): any two roots `x, y < p` of `x² ≡ −1` satisfy `x = y` or
`x + y = p`.  The proof reduces `p ∣ x²+1` and `p ∣ y²+1` to `p ∣ (x−y)(x+y)` (the difference of
squares, `sq_expand`), then applies **Euclid's lemma** `euclid_via_inverse` (`x−y` is invertible
mod `p` when `0 < x−y < p`, from the modular inverse) to force `p ∣ (x+y)`, whence `x+y = p`
(`eq_p_of_dvd`: the only multiple of `p` in `(0, 2p)`).

This extends to **every odd prime power** (the full Button/Zhang class): `two_roots_of_prime_pow`
shows `SqrtNegOneTwoRoots (p^(k+1))` for odd prime `p`.  The new ingredient is that `p` divides
at most one of `x−y, x+y` (else `p ∣ x`, impossible since `x² ≡ −1`); the coprime one is coprime
to `p^(k+1)` (`coprime_prime_pow`, from `dvd_prime_pow_cases`: divisors of `pᵏ` are `1` or
multiples of `p`) and cancels via the fully general Euclid's lemma `euclid_of_coprime`.  So the
reduction's hypothesis is discharged at every prime-power maximum; the remaining open step is the
residue-map injectivity above.

What is established directly: the conjecture itself at small maxima, `MarkovMaxUnique` for
`c = 5, 13, 29` (assembled from the decidable single-pair checks `markov_max_unique_{5,13,29,34}`);
the input `SqrtNegOneTwoRoots` for the prime powers `5, 13, 25` and the prime `29`; and the
boundary case `not_sqrtNegOneTwoRoots_65`, where `c = 65 = 5·13` already carries the four roots
`{8, 18, 47, 57}` and the pair `8, 18` breaks the two-roots input — the first place the open
difficulty appears.

## The `p ≡ 3 (mod 4)` obstruction

Because every prime factor of a Markov number admits a square root of `−1` through the neighbor
congruence, and `x² ≡ −1 (mod p)` is unsolvable when `p ≡ 3 (mod 4)`, no prime `≡ 3 (mod 4)`
divides a Markov number — every odd prime factor is `≡ 1 (mod 4)`.

This unsolvability is proved **generally** (not just per prime) in
`ModArith/MarkovPrimeFactor`: `no_sqrt_neg_one_4k3` shows that for `p = 4k+3` satisfying the
prime-gcd hypothesis (the ∅-axiom proxy for primality used by the repo's Fermat little theorem
`universal_flt_main`), there is no `x` with `p ∣ x²+1`.  The argument is `x^(p−1) = (x²)^(2k+1) ≡
(−1)^(2k+1) ≡ −1` (`neg_one_odd_pow_mod`, `pred_mod_of_dvd_succ`), contradicting Fermat's
`x^(p−1) ≡ 1` and forcing `p ∣ 2`.  Concrete primes follow by the repo's per-prime gcd witnesses
(`no_sqrt_neg_one_mod_{7,11}` from `prime_gcd_{7,11}`); the solvable contrast `5, 13`
(`p ≡ 1 mod 4`) is in `MarkovUniqueness`.

The two halves then meet: `markov_reachable_no_3mod4_factor` proves **no prime `≡ 3 (mod 4)`
divides a reachable Markov number `c > 1`** (Zhang 2007).  A `√(−1)` exists mod `c`
(`markov_reachable_neg_one_qr`), so it would descend to a `√(−1)` mod any prime factor `p`; but
`no_sqrt_neg_one_4k3` forbids that for `p ≡ 3 (mod 4)`.  So every odd prime factor of a Markov
number is `≡ 1 (mod 4)` — the existence half (the uniqueness machinery) and the non-existence
half (the prime-factor obstruction) closing on each other.

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

## The spine as a linear recurrence; the residue as a Casoratian

The golden spine is `C`-finite: the odd-index Fibonacci numbers satisfy the trace-`NS` recurrence
`fib(2n+1) + fib(2n+5) = 3·fib(2n+3)` (`fib_spine_recurrence`), characteristic polynomial
`x² − 3x + 1` — the characteristic polynomial of the golden matrix `P = [[2,1],[1,1]]` (trace
`3 = NS`, det `1`) whose orbit is the spine, the recurrence step being the Markov-Vieta jump
itself.  The Pell/silver spine is the companion with coefficient `6` (`pell_spine_recurrence`,
char. `x² − 6x + 1`).  So `NS = 3` is the Markov coefficient, the trace of `P`, and the spine
recurrence coefficient at once.

Read in the discrete-difference calculus, `fib_spine_sqrt_neg_one` (`fib(2n+2)² + 1 =
fib(2n+1)·fib(2n+3)`) is the **Casoratian** (discrete Wronskian, cross-determinant of two
solution windows) of this recurrence, pinned to the constant `±1` by Cassini; reduced mod the
spine's Markov number it is the `√(−1)` residue.  In the forward-difference calculus the spine's
annihilator is `Δ² − Δ − 1` — *the golden ratio's minimal polynomial* — whose **nonzero constant
term** is exactly why the spine is strictly `C`-finite, not poly-depth (a poly-depth sequence is
killed by a pure `Δ^k`).  This is the precise alignment of the infinite-forward-difference-depth
boundary with the holonomicity markers (`QuasiPolyCF ⊊ C-finite`, like `2ⁿ`); the
Markov/quadratic-irrational sector meets the polynomial-depth sector only at the constants.  The
Vieta jump `c ↦ 3ab − c` is itself the difference reflection on the state (`vieta_reflection`:
`c + c' = 3ab`, involution `3ab − c' = c`).

This also reframes the open crux.  The Markov tree is a coalgebra; labelling each triple by its
maximum and reading off the `√(−1)`-residue is an observable, and the uniqueness conjecture says
the labelling is **minimal/reduced** (distinct triples have distinct labels — the residue
separates states, Myhill–Nerode).  The arc supplies reachability and determinism; uniqueness is
the missing reducedness.  The reduction `#roots ≤ 2 ⟹ unique` says the observable separates when
it takes ≤ 2 values (prime powers); at composite `c` it takes `2^ω ≥ 4` values and stops
separating — so an extra observer is needed.  `markov_phantom_root_filter` is the first such
filter, at the smallest composite `c = 65 = 5·13`: the four roots `{8,18,47,57}` explode, yet
`markovEq · · 65` admits no triple — every root is *phantom*, and the primitive Diophantine
descent constraint is what filters them.

`markov_composite_separation` then advances the mechanism to the **first real composite Markov
number** with the explosion, `c = 1325 = 5²·53` (four roots `{182,507,818,1143}`).  Here `markovEq`
separates them exactly: the valid pair `{507,818}` recovers the actual triple `(13,34,1325)` via
`a = (u·b) mod c` (`507↦b=34⇒a=13`, `818↦b=13⇒a=34`), while the phantom pair `{182,1143}` closes
no triple (`∀ b < 1325, ¬ markovEq ((u·b)%1325) b 1325`).  Since any triple `(a,b,1325)` has root
`a·b⁻¹` among the four and the `∀b¬` rules out the phantom pair, uniqueness holds at `1325`
*structurally* — the first such separation at a genuine composite Markov number, exactly where the
general conjecture is open.

## Full uniqueness at `1325`, unconditionally (`markov_max_unique_1325`)

The separation above is upgraded to the named predicate `MarkovMaxUnique 1325` — *every* ordered
triple with maximum `1325` is `(13,34,1325)` — and then made **unconditional**, ∅-axiom, with no
hypotheses.  The first complete Markov uniqueness theorem at a four-root composite Markov number.

Two moves replace the infeasible two-dimensional `∀a ∀b` enumeration (which stack-overflows the
kernel at `c = 1325`):

  1. **The 2-D→1-D reduction** (`markov_root_recovery`).  A triple `(a,b,c)` with `gcd(b,c)=1`
     produces the residue `u = (a·b⁻¹) mod c`, which is *both* a root of `−1`
     (`(u·u+1)%c = 0`, via `mod_root_of_dvd_sq_succ` descending the divisibility witness to its
     residue) *and* recovers the smallest entry (`a = (u·b) mod c`, `markov_recovery`).  So a
     triple is pinned by the pair `(u,b)` with `u` in the *finite* root set
     (`sqrtNegOneRoots_1325`: exactly `{182,507,818,1143}`).  Uniqueness becomes a four-way case
     split, each a one-dimensional decidable search over `b` (`markov_root_{182,1143}` phantom,
     `markov_root_{507,818}` valid) — assembled by `markov_max_unique_of_single` and
     `markov_max_unique_1325_of_coprime`.

  2. **Coprimality by Markov's descent theorem** (`markov_hcop_general`).  The reduction needs
     `gcd(b,1325) = 1`.  This is the *primitivity* of Markov triples, and it now holds for **every**
     triple, unconditionally.  The descent engine (`markov_descent_ineq`: `a²+2b² ≤ 3ab²`;
     `markov_vieta_partner_le`: the down-move `c' = 3ab − c ≤ b < c`) drives a structural recursion
     `reachable_of_fuel` (bounded by a fuel `≥ c` — plain `Nat.rec`, no `WellFounded.fix`, so
     ∅-axiom): any ordered triple with `c ≥ 2` descends to `{a, b, 3ab−c}` whose maximum is
     `b < c`, terminating at the root `(1,1,1)`.  Hence `markov_ordered_reachable` — every ordered
     Markov triple is on the tree — and `markov_ordered_coprime` — every triple is pairwise coprime
     (composing with the tree invariant `markov_reachable_coprime`).  `markov_hcop_general c`
     (`c ≥ 2`) packages this as the coprimality input for *all* maxima at once.

The route is packaged once and for all as `markov_max_unique_of_4roots` (and its two-root twin
`markov_max_unique_of_2roots`): given the root set as a decidable disjunction and one certificate
per root (each a 1-D `decide` over `b`), it returns `MarkovMaxUnique c`, with coprimality, `a ≥ 1`,
and `b < c` all discharged internally by the descent theorem and the recovery map.  A new Markov
number is then a single line.  Closed so far, all ∅-axiom and with no per-`c` coprimality
argument: the 4-root composites `1325 = 5²·53` `(13,34)`, `985 = 5·197` `(2,169)`, `610 = 2·5·61`
`(1,233)` (the first **even** composite); and the 2-root prime / prime-power class
`169 = 13²` `(2,29)` (the first **prime-power composite**, the Button/Zhang case), `233` `(1,89)`,
`433` `(5,29)`.

## Pairwise coprimality is the tree's invariant

The square-root encoding needs `b` invertible mod `c`, i.e. `gcd(b,c) = 1`.  This is not an
extra assumption: pairwise coprimality is the **invariant** of the Vieta generation.  At the
root `(1,1,1)` it is trivial, and a Vieta jump `c ↦ c' = 3ab − c` preserves it, because
`gcd(a,c') = gcd(a,c)` — any common divisor `g` of `a` and `c'` divides `3ab` (through `a`) and
`c'`, hence divides `c = 3ab − c'`, hence divides `gcd(a,c) = 1` (`coprime_vieta_step`).  Over an
explicit reachability predicate (`MarkovReachable`: root, Vieta jump on the last entry, and the
two transpositions), induction then gives `markov_reachable_coprime`: **every tree triple is
pairwise coprime**, with `markov_reachable_gcd_bc` extracting the `gcd(b,c) = 1` the encoding
needs.  `markov_reachable_is_triple` confirms the predicate is sound — every reachable triple
satisfies `x²+y²+z² = 3xyz` (via `markov_vieta` on jumps, `markov_symm` on transpositions) — so
these are genuine, pairwise-coprime Markov solutions, not an empty class.  And once an inverse is
in hand in residue form `(b·b') % c = 1`, `neg_one_qr_of_mod` fires the encoding directly.

## The encoding fires unconditionally

The coprimality invariant and the `√(−1)` encoding combine without any leftover hypothesis.  The
xgcd-correctness bridge `MarkovPrimeFactor.inverse_of_coprime` turns `gcd(a,m) = 1` into an
explicit modular inverse `(a · (modBezout a m).2) % m = 1 % m` — proved via `xgcdAux_dvd_both`
(the xgcd gcd-component divides both inputs, under the bound `fuel ≥ r₁ + 1`, which `modBezout`'s
`a+m+1` satisfies since `r₁` strictly decreases).  Since `markov_reachable_gcd_bc` gives
`gcd(b,c) = 1` on every tree triple, `markov_reachable_neg_one_qr` concludes: **for every
reachable Markov triple with maximum `c > 1`, `c ∣ (a·b⁻¹)² + 1`** — the square root of `−1` mod
`c` exists structurally, with no invertibility assumption.  This closes the chain from the tree's
coprimality to the encoding.

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
Reports `52 pure / 0 dirty`.
