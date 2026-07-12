# Divergence conjecture slate — 2026-07-12

Companion to `research_program_year_horizon.md`: where the program lists
*topics*, this note stakes *conjectures* — sharp, falsifiable, 213-native
statements a successor can attack (or kill) directly.  Tier-1 volatile.
Each entry: statement, why it should be true (or is worth killing), the
kill-test.  Status tags: [K] killable in one session, [A] arc, [M] marathon.

---

## S1. Crystallographic reciprocity ceiling [A]

**Conjecture.**  The pair-symmetric reciprocity schema (the
`mu3_reciprocity_algebra` finite closer + `muK_eq_of_modEq` separation)
closes the k-th power reciprocity law exactly for `k ∈ {2, 3, 4, 6}` — the
crystallographic unit orders (`φ(k) ≤ 2`), i.e. the value group `μ_k` lives
in a *quadratic* cyclotomic ring (ℤ, ℤ[ω], ℤ[i]).  For `k = 5` the same
schema does NOT close (ℚ(ζ₅) has degree 4; the symmetric-pair relation
underdetermines the symbol).

**Why.**  The cubic closer worked because distinct μ₃ values differ by a
norm-3 element in a rank-2 ring — a rank-2 phenomenon.  This would make the
`{1,2,3,4,6}` crystallographic restriction (already forced in the matrix
and unit-group arcs) *also* the reciprocity horizon: one restriction, third
appearance.

**Kill-test.**  Build B2 (the generic engine); if quartic needs a genuinely
new mechanism beyond rank-2 separation, S1 dies.  Either outcome is a
theorem-shaped fact about the schema.

## S2. CLT is rung 2 of the modulus-degree ladder [A]

**Conjecture.**  The discrete de Moivre–Laplace bracket (blueprint 21,
Phase PB) has rate-modulus degree exactly 2 in the `RateModulus` /
`RateStratification` sense: the two-sided bracket on
`C(2n, n+k)/C(2n, n) = Π_{j≤k} (n−j+1)/(n+j)` narrows at the `k²/n` scale
and at no coarser rung.  I.e. the Gaussian shape IS the degree-2 slot of
the existing rate hierarchy — the probability rebuild lands *inside* the
`Real213/Modulus` ladder rather than beside it.

**Why.**  The ladder already proves the hierarchy is strict and occupied at
every rung; the central-binomial product is the most natural degree-2
candidate the corpus already owns (`central_binom` machinery).

**Kill-test.**  Prove the product's two-sided bounds and compute its
`rootFloor`-degree; if it lands at degree 1 (generous) or needs a
non-integer rung, S2 dies and the failure localizes what "Gaussian" means
internally.

## S3. The ℚ-cup and the 2-torsion reduction [M]

**Conjecture.**  A normalized ℚ-valued cup product on `K_{3,2}` exists
(graded-commutative, Leibniz-compatible with the closed CupAW family), and
(i) its `k=1` self-pairing term forces the Gram `1/d²` prefactor (the E1
forcing theorem), and (ii) **the existing Bool/F₂ cup is its 2-torsion
reduction** — i.e. the corpus's invariant-structure finding "B is A's
2-torsion where a character exists" (`invariant_structure.md` (iv))
instantiates at the cup-ring scale: F₂-cup = (ℚ-cup) mod 2.

**Why.**  The `1/d`-per-factor rule is *proven not derivable* from the F₂
cup — the obstruction is exactly that F₂ forgets magnitude, which is what
"B = A's 2-torsion" predicts.  If the A/B structure is real, the ℚ-cup is
where A lives.

**Kill-test.**  Construct the ℚ-cup on the 2-skeleton (finite data); check
Leibniz.  If graded-commutativity and the `1/d` graduation cannot coexist,
S3(i) dies and the α_em assembly gap is proven deeper than an interface.

## S4. The octet double-count isomorphism [A]

**Conjecture.**  The `8 = NS²−1` of the gauge sector is a *count
isomorphism*, not a numerological coincidence: the incidence-Fubini
double-count of the regular representation of a 3-object distinguishing
system (blueprint 19, Phase RE: `|G| = Σ dᵢ²`, adjoint = regular minus
trivial) and the cohomological `b₁(K_{3,2}^{(c=2)})` are two Lens readings
of one ∅-axiom bijection — provable as an explicit map, replacing both the
`Unit`-model coker and the `decide` that bakes in `c = 2`.

**Kill-test.**  Build the two counts; exhibit the bijection or exhibit the
obstruction.  A negative here is important: it would show the gauge-`8`
identification genuinely needs the classical LES import.

## S5. The neutrino zero-dial mass-floor falsifier [K]

**Observation → conjecture.**  The corpus's mass-*ratio* reading
(`m₃/m₂ ≈ 5.71`, Fibonacci) plus the *measured* `Δm²₃₁/Δm²₂₁ ≈ 33.8`
jointly over-determine the lightest mass: with `r = m₃/m₂` fixed, the
measured splitting ratio solves for `(m₁/m₂)²` with **zero dials**.
**Conjecture:** the solved `(m₁/m₂)²` is non-negative and JUNO-era
consistent — i.e. the Fibonacci ratio survives the second, independent
measured number.  If the implied `(m₁/m₂)²` is negative, the Fibonacci
mass-ratio reading is **falsified** (cleanly, by arithmetic).

**Why this is the right shape.**  E7's problem is too few *independent*
pinned numbers; this adds one at S-size — the check is a rational
inequality, ∅-axiom once the bracket arithmetic is stated.

**Kill-test.**  One session: state the bracket, plug the PDG windows,
`decide`.

## S6. Sedenion zero-divisor census is CD-forced [A] — **EXECUTED, core landed**

**Verdict (2026-07-12).**  The census is fully rigid in the repo's
nested-CD encoding (interpreter-verified over the whole `15⁴·2` sweep;
witness-row facts kernel-certified PURE in
`Levels/SedenionZeroDivisorCensus.lean`):

  * left pairs with partners = `(a, b)`, `a ∈ 1..7` (octonion imaginary),
    `b ∈ 9..15`, `b ≠ a+8` — **42 pairs** (7×6);
  * each has exactly **4** `(c<d, ±)` partners;  **total = 42·4 = 168**.

`168 = |PSL(2,7)|` (Fano-plane automorphisms — the octonion table's own
symmetry count) is the natural Lens tag; proving that identification
(orbit-transitivity of the census under the table's automorphisms) is
the remaining conjectural half, together with the 15-row kernel ledger
(`aCount a = 24` measured ∅-axiom-certifiable at ~2 min/row; kept out of
the always-built tree).  The finite signature of the L4 associativity
loss is `(42, 4, 168)`.

**Conjecture.**  The combinatorial skeleton of the sedenion zero-divisor
locus (which basis-pair products vanish, over the ℤ-basis of the L4
Cayley–Dickson double) is a finite count forced by the doubling functor's
order-4 twist alone — computable by `decide` over the 16-element basis,
with the count reading as the associativity-loss count-Lens (each CD
doubling loses one law; at L4 the loss becomes *visible as objects*).
This gives the tower its own `object1_not_surjective` moment: the first
rung where the self-cover's failure is inhabited, not just stated.

**Kill-test.**  Finite: build L4 multiplication (the L1/L2 functor
iterates), enumerate, count.  Whatever number appears is then either
forced (provable from the twist) or presentation-dependent (also a
finding).

## S7. Reciprocity is Frobenius-splitting, once [A]

**Conjecture.**  One theorem schema
`frobenius_splitting_iff_residue_symbol` states quadratic AND cubic (and,
if S1 holds, quartic) reciprocity simultaneously: the residue symbol of
`p` in the value ring is the Frobenius-reading of `p`'s splitting — the
law is one Lens-symmetry, and the classical case split (inert/split) is
the two-valuedness of the splitting Lens.  Blueprint 20 (Phase GE) is the
carrier; the corpus's `fp2Frob` and the conjugation-flips-the-modulus
essay are the proven halves.

**Kill-test.**  State the schema over the closed QR + cubic cases; if the
two cases don't factor through one statement without a case-split *in the
statement*, S7 dies (and the case-split location is itself a finding
about what "one law" can mean internally).

## S8. W1-completeness (the triage table is a theorem-in-waiting) [M]

**Meta-conjecture.**  Within the corpus's reach, W1 is *complete*: every
quantity that is (i) an unsigned monotone count with (ii) an elementary
two-sided estimate closes ∅-axiom — no third obstruction exists below
signed cancellation.  Operationally: any frontier that resists ≥3 sessions
will, on post-mortem, be classifiable W2/W3/W4 — never "W1 but stuck".

**Why it matters.**  If S8 holds through a year of verdicts, the triage
table (§0 of the program) is promoted from doctrine to empirical law of
the framework — the strongest available *internal* evidence that the
count-Lens boundary is real and sharp.  If a genuine W1-but-stuck case
appears, that case is the most interesting object of the year.

**Kill-test.**  Maintain the table; every stuck frontier gets a filed
verdict.  (This is a ledger conjecture — killed or confirmed by
accumulation, not by one proof.)

## S9. Noble numbers are the three-distance degeneracy locus [A]

**Conjecture.**  In the three-distance theorem (program C7), the
parameters `α` whose gap spectrum degenerates to *two* lengths infinitely
often are exactly the noble numbers (CF tail all-1s, the φ-orbit) — tying
the Markov spectrum's discrete bottom (`< 3`, closed families) to a pure
counting statement: the Lagrange-spectrum extremality of φ IS a gap-count
degeneracy, W1-visible without any measure theory.

**Kill-test.**  Prove the φ case (Fibonacci denominators, Zeckendorf
machinery exists), then one non-noble quadratic counterexample.

## S10. Kraft equality is the complete distinguishing tree [K→A]

**Conjecture.**  The Kraft inequality `Σ 2^{−lᵢ} ≤ 1` for prefix-free
codes is `Raw.leaves` bookkeeping (each codeword = a leaf of a binary
distinguishing tree), equality iff the tree is a *complete* self-cover of
its depth — i.e. Kraft-equality codes are exactly the finite faithful
covers, and the strict-inequality deficit `1 − Σ2^{−lᵢ}` is the residue's
count at the code scale.  Entropy's source-coding bound then reads as: the
residue cannot be coded away (a finite-scale `object1_not_surjective`).

**Kill-test.**  PA-level: formalize over `List Bool` prefix-freeness;
the equality case is structural induction.  If the deficit does not
compose the way the residue calculus predicts (additivity under tree
grafting), the "residue at code scale" reading dies while the inequality
survives as a plain W1 brick.

## S11. The Ramanujan ladder rides the primorial keystone [A]

**Conjecture.**  Once Bertrand closes (the recommended first marathon),
the whole ladder `π(x) − π(x/2) ≥ k` (Ramanujan-prime thresholds `R_k`)
is W1 uniformly: each `R_k` admits a computable bracket from the same
primorial keystone `∏_{p≤N} p ≤ 4^N` + Erdős binomial bookkeeping, with
no new analytic input up the ladder.  I.e. Bertrand is not an endpoint
but the `k=1` rung of a W1-uniform family — a clean test that "one more
prime in the window" never crosses into W2.

**Kill-test.**  After Bertrand: prove `k=2` from the same cone; if the
constant degrades faster than the keystone allows, locate the first `k`
where elementary bookkeeping fails and file the boundary.

---

## How to use this slate

Attack order that maximizes information per session:
**S5** (one session, adds an independent falsifier either way) →
**S6** (finite, `decide`-terminal) → **S2** (welds two programs) →
**S4/S7** (the two identification welds) → **S1** (rides B1/B2) →
**S3** (the heavy cut) — with **S8** as the standing ledger and
**S9/S10/S11** as discipline-seed companions.

A killed conjecture here is a *result*: file the kill in the program's §0
triage table with its class, and the slate has done its job.
