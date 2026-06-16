# Cross-domain: divisor-theory marathon ↔ main (branch-merge observations)

Recorded at the merge of `claude/multi-agent-math-research-n68ovi` (the
multiplicative-divisor-theory + sequences + inequalities marathon) into the
state of `main` (the physics-branch forced/read + descent-schema + gravity
work). Two connections look genuine; one softer. Honest scoping below.

## 1. σ-parity strong induction IS a UFD-descent instance (solid)

`SigmaParityComplete.sigma_odd_square_odd` (odd `m`: `σ(m)` odd ⟺ `IsSquare m`)
is proved by **smallest-prime-power strong induction**: extract `m = p^k·m'`
(`exists_prime_pow_cofactor`), recurse on `m' < m`, glue with multiplicativity.
That is exactly the shape catalogued in `general_theory_metaanalysis.md` /
`universal_descent_schema.md` (the iterated-descent schema: GCD / UFD / Markov /
Ricci — descend by a monovariant to a fixed base).

The sharpening main's descent schema gains: the UFD rung is not only "gcd
descends to 1" — **any multiplicative arithmetic function's value is forced by
descent over the factorization**, with the function's behaviour on prime powers
(`sigma_odd_prime_pow_parity`) as the per-step datum and the monovariant `m↓`.
`sigma_odd_square_odd` is a concrete relational instance (the value-parity is
forced, not just the gcd). Candidate addition to the descent catalogue as a
**multiplicative-function-descent** member — the same shape as
`VpSeparationDescent` (already filed as the number-theory descent instance) but
carrying a *function value* down, not just a separation.

Open: is "multiplicative-function descent" a distinct rung or the UFD rung read
through the counting Lens? (Likely the latter — factorization = the UFD descent,
the function just rides it.) Worth one line in the descent metaanalysis.

## 2. Involution-parity = fixed-point-count mod 2 (recurring Z/2 shape)

`TauParity.doubleSum_parity` — for symmetric `g`, `Σ_{a,b<N} g a b ≡ Σ_a g a a
(mod 2)` (off-diagonal `(a,b)/(b,a)` pairs cancel) — is the engine of τ-parity
(divisor involution `d ↔ n/d`, fixed point `√n`). The **same Z/2-involution /
fixed-locus-counted-once shape** appears on the physics branch in the cohomology
constant-mode count: `bcount_const`, the involution complement
`im_count_inj_complement`, and the essay `the_minus_one_under_three_lenses`
(one residue's lone constant mode counted once). Both are "a Z/2 action's parity
invariant = its fixed-point count mod 2," in different categories (divisor lattice
vs. cochain complex).

Softer than #1 — it may be analogy rather than one structure. The test: is there
a single 213-native statement (a `Bool`/`Z/2` involution lemma) that both
`doubleSum_parity` and `im_count_inj_complement` instantiate? If yes, that lemma
is the shared core; if the fixed loci differ in kind (a diagonal `{(n,n)}` vs. a
kernel constant mode) it stays an analogy. Not yet attempted.

## 3. (noted, thin) Lucas norm ↔ Markov/Cassini quadratic invariants

`LucasSequences.lucasQuadratic` (`V_n²−D·U_n²=4Q^n`) is the general Pell/norm
form; main carries `CassiniUnimodular` and the Markov triple norm
(`x²+y²+z²=3xyz`). Both are "quadratic-form invariants of a second-order
recurrence." Connection is real but likely too generic to be load-bearing —
recorded only so it is not re-noticed as new.

## Status
Open observations from the branch merge. #1 is a concrete candidate for the
descent catalogue; #2 is a test (find-the-shared-lemma) not yet run; #3 is parked.
