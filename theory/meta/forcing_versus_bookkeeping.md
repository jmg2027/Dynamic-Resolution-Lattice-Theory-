# When ∅-axiom forces different mathematics (vs. bookkeeping)

A methodological distinction for reading what a PURE (∅-axiom) re-derivation of
a classical theorem actually shows. Not every ∅-axiom proof carries the same
evidential weight; the difference is whether the constraint *forced a different
proof* or merely *removed the ambient library's incidental axiom use*.

## The two kinds of PURE proof

A classical theorem (Euler, CRT, De Morgan, …) exists in standard libraries
**with** axioms — `propext`, `Classical.choice`, `Quot.sound`,
`native_decide` — because those libraries are *built on* them. Re-deriving the
theorem ∅-axiom can mean two very different things:

- **Bookkeeping PURE** — `PURE = (standard proof) − (axiom import)`. The proof
  shape is unchanged; only lemmas are swapped for residue-internal twins
  (`Nat.dvd_trans → dvd_trans_213`, `rw`-on-`Iff` → `.mp/.mpr`, `funext` →
  pointwise, `Nat.mul_mod_left → NatDiv213.…`). Real, but the only thing
  established is that the *library's* axiom use was incidental for this theorem.
- **Forcing PURE** — requiring ∅-axiom makes the proof *change shape*, and the
  new shape **exposes constructive content** the classical proof hid: an
  explicit witness, an algorithm, a representative-level operation. Here the
  theorem turns out to be reachable *by a route classical mathematics does not
  take* — evidence that the result was residue-native and the classical
  packaging non-essential.

`#print axioms` is the meter, but it measures the *pointing's* contamination,
not the theorem. A theorem is neither Lean file; both are pointings at the same
residue read under one Lens (`FlatOntologyClosure.object1_not_surjective` at the
proof level — no proof *is* the theorem, but pointings differ in how much they
import). The bookkeeping/forcing split is the difference between *a smaller
pointing of the same shape* and *a structurally different pointing that reveals
more*.

## Three veins of genuine forcing

- **A — Quot.sound avoidance.** A theorem classically about a *quotient*
  (`ℤ = ℕ²/∼`, `ℚ = pairs/∼`, `ℤ/n`, group quotients), proven on
  *representatives*. Reveals: the quotient was packaging; the operation lived on
  the representative all along ("the tuple IS the number",
  `math/numbersystems/slot_arithmetic.md`).
  - `ModArith/CRTReconstruction` — CRT as the explicit reconstruction bijection
    `crtSolve` (Bezout closed form), not the quotient-ring iso `ℤ/mn ≅ ℤ/m×ℤ/n`.
    *The isomorphism is literally the reconstruction algorithm.*
  - `ModArith/FieldIffPrime` — `ℤ/n` is a field ⟺ n prime, on residues:
    invertibility decided by Bezout, non-field exhibited as an explicit zero
    divisor `(a·b)%n = n%n = 0`. *The field dichotomy is the gcd computation.*
  - `NumberTheory/UnitsOfZn` — the multiplicative group `(ℤ/n)^×` on
    representatives: a unit is a coprime residue, closure under `·` mod `n` is the
    gcd fact `gcd(ab,n)=1`, inverses are Bezout, and the order is `φ(n)`
    *definitionally* (`unit_count_eq_totient := rfl`). *The group structure lives
    on the coprime-residue set; the quotient ring was packaging.*
- **B — Classical / LEM avoidance.** An existence theorem classically by
  *minimal counterexample / `by_contra`* (LEM + well-ordering), re-proven by
  *explicit descent / bounded search*. Reveals: the witness / algorithm.
  - `NumberTheory/EulerTheorem` — the Lagrange route ("order ∣ φ(n)") is
    **circular for composite n** (order-divides-totient *needs* Euler), forcing
    the **totative-product permutation** proof. *Euler is a permutation-invariance
    fact, not a group-order corollary.*
  - `ModArith/WilsonConverse` (`exists_nontrivial_factor`) — "least divisor > 1
    is prime" (well-ordering) becomes a **bounded prime search**: an explicit,
    computed factor.
  - `NumberTheory/PrimesThreeModFour` — **infinitely many primes `≡ 3 (mod 4)`**
    (`∀ N, ∃ p, N < p ∧ prime p ∧ p%4=3`). The classical proof posits a finite
    exhaustive list and contradicts it (LEM + finiteness). ∅-axiom drops both:
    given `N` it *constructs* `M = 4·N!−1` and *computes* `M`'s least `≡3 mod4`
    prime factor (keystone `exists_prime_factor_3mod4`, least-factor recursion),
    which is `> N`. *The new prime is an algorithm output, not a prime extracted
    from a refuted minimal counterexample.* (14 PURE.)
  - `NumberTheory/FermatQuartic` — **`x⁴+y⁴=z²` has no positive solution**
    (`no_quartic_sq`, hence `no_quartic_quartic`). The textbook proof is the
    archetypal *minimal-counterexample* (least `z`, well-ordering + LEM). ∅-axiom
    has no well-ordering as a proof device, so the descent becomes an explicit
    `Nat.strongRecOn` on `z` whose step **constructs** the strictly-smaller
    solution `(a,b,c)` — two Pythagorean-converse inversions + the coprime-square
    split *returning* `a=√r, b=√s, c=√(r²+s²)`. *"No solution" = "the
    `z`-decreasing constructor cannot keep terminating"; the descent map is the
    content, not a contradicted minimality.* (29 PURE, Nat-native.)
  - `NumberTheory/TwoSquareTheorem` — **Fermat's two-square theorem, hard
    direction** (`p ≡ 1 mod 4 ⟹ p = a²+b²`), the capstone B-case. The classical
    Thue-lemma + size-descent proof is non-constructive throughout (a pigeonhole
    `∃` + minimal-counterexample). ∅-axiom localizes *all* of it to "produce the
    box collision": `exists_collision_lt` returns the colliding pair of
    `Fin (q²) → Fin p`, the witness `(a,b)` is read off by `i ↦ (i/q, i%q)`, and
    the "multiple of `p` below `2p` is `p`" step is a literal computation. *The
    two-square witness is an algorithm output, not an existential.* (19 PURE.)
  - `Combinatorics/ErdosSzekeres` — a sequence of `> (r−1)(s−1)` distinct values
    has a strictly-increasing length-`r` or strictly-decreasing length-`s`
    subsequence (with the subsequence *extracted*, choice-free). Classical proof
    is an abstract pigeonhole `∃` on `(inc,dec)` labels wrapped in `by_contra`;
    ∅-axiom packs the labels into `Fin ((r−1)(s−1))`, `exists_collision_lt`
    *returns* the colliding pair, and the strict-order step overflows the box.
    *The monotone-run witness is an algorithm output.* (29 PURE.)
  - `NumberTheory/DividesPairPigeonhole` — "among any `n+1` numbers in `[1,2n]`,
    one divides another." The classical pigeonhole asserts a non-constructive `∃`
    (two share an odd part — *which* pair unstated). ∅-axiom forces the witness
    twice: `same_oddpart_dvd` reads `a ∣ b` straight off the 2-adic valuation
    comparison (explicit cofactor `2^(v2 b − v2 a)`), and the collision must be
    *produced* — which forced a new reusable primitive
    `Combinatorics/Pigeonhole.exists_collision` (a decidable scan + `shiftAround`
    recursion *returning* the colliding indices, where the prior `no_inj_lt` only
    refuted injectivity → `False`). *The constructive content of pigeonhole is the
    witness-returning form; the dividing pair is computed, not asserted.* (Two
    independent agents converged on this exact shape — the route is forced.)
- **C — non-effective → effective.** A classically non-effective existence
  forced into a *modulus / constructor*. Reveals: the rate / the construction.
  The corpus modulus programme and the `Math/Logic/` omniscience hierarchy
  (LLPO / WKL / König / Heine-Borel) are the meta-catalogue of *exactly where*
  classical logic imports — i.e. where forcing is unavoidable.
  - `Real213/Bisection/CutBisection` + `Analysis/DyadicSearch/RootCertificate`
    — the constructive intermediate-value theorem. Classical IVT bisects by
    *deciding* `f(m) ≷ 0` (LEM on the reals); ∅-axiom forces the explicit dyadic
    bracket + modulus, and *the rate of convergence is the content*. Note vein C
    is the corpus's **native** mode — it has no classical non-effective IVT to
    contrast, because 213 does all analysis modulus-first. Where classical math
    imports LEM for existence, 213 was already constructive.
  - `Analysis/ExtremeValue` — the **Extreme Value Theorem**, modulus form.
    Classical EVT *attains* the max at a located point (LEM). ∅-axiom forces:
    the supremum *value* `Msup` is a computable real (`CauchyCutSeq.limit` with a
    convergence modulus from the uniform-continuity modulus), *located* (approached
    by a finite-resolution grid-max), bounding `f`, and **attained at every finite
    resolution** — but the argmax *moves with the resolution*, so the true
    maximizer is the `n→∞` limit, **reached by none** (`object1_not_surjective` at
    the analysis level). *The modulus, not a maximizing point, is the computable
    content classical EVT hides.* (23 PURE.)
  - `Logic/BolzanoWeierstrass` — the **honest other half**: some analysis theorems
    are *not* unconditionally ∅-axiom. Binary BW (every `{0,1}`-sequence has a
    convergent subsequence) genuinely needs an omniscience principle, so the
    ∅-axiom result is the *calibration*: `lpo_of_bw : BW → LPO` (the strongest base
    rung), with the constructive cores `subseq_of_unbounded_true` /
    `subseq_of_eventually_false` (∅-axiom once the witness is data). `bw_of_lpo` at
    plain LPO is *not* provable — the extraction needs deciding a Π⁰₂ statement,
    above the ledger. *The classical choice/LEM is not removed — it is named (LPO)
    and measured (Π⁰₂); the calibration implication is the theorem.* This is the
    `Math/Logic/` omniscience ledger doing exactly its job: locating where the
    import is unavoidable, per the no-exterior guard ("say plainly when no internal
    handle is found"). (13 PURE.)

  - `Logic/HeineCantor` — **Heine–Cantor** ("pointwise-continuous on `[0,1]` ⟹
    uniformly continuous") calibrated against the **fan theorem**: the ∅-axiom
    `heineCantor_of_fan` upgrades pointwise to uniform continuity given the fan
    theorem (hypothesis), bracketed by `bar_of_pointwiseCont` (pointwise ⟹ `Bar`)
    and `uniform_of_bounded` (`Bounded` ⟹ uniform modulus), both ∅-axiom. The fan
    theorem is the load-bearing bridge `Bar → Bounded`. *HC's compactness is named
    as the fan theorem* — a ledger entry dual to WKL. (10 PURE.)

  - `Analysis/UniformLimitContinuous` — **the uniform limit of continuous
    functions is continuous**, modulus form (unconditional ∅-axiom). The classical
    `∀ε∃δ` "3ε" theorem becomes `uniform_limit_continuous`: the limit's continuity
    modulus is *computed*, `Ω m = ω_{r(m+2)}(m+2)`, from the convergence rate `r` +
    one `f_n`'s modulus (quarter-triangle `qtri` sums the three `1/2^(m+2)` gaps).
    No compactness/omniscience. *The modulus is the theorem.* (20 PURE.)

  - `Logic/Dini` — **Dini's theorem** calibrated to the fan theorem (sibling of
    Heine–Cantor): a monotone pointwise-convergent sequence converges uniformly,
    given the fan theorem. Monotonicity is the load-bearing ingredient that turns
    the per-interval bound into a uniform convergence index. (14 PURE.)
  - `Logic/RealDichotomyLLPO` — the **analytic-LLPO** calibration, two-sided: the
    real sign-dichotomy `∀ x, x ≤ 0 ∨ 0 ≤ x` IS LLPO (`llpo_of_realDichotomy` +
    converse). This locates exactly why the *exact* IVT / bisection's sign step
    cannot be ∅-axiom — deciding the sign of the encoded cut is LLPO — while the
    corpus's *approximate* IVT (`cutEq … 0`) stays pure by never making the global
    sign verdict. The "denominator blow-up" in the separating probe is the
    omniscience cost made visible. (31 PURE.)

  - `Analysis/BanachFixedPoint` — the **Banach contraction-mapping theorem**,
    modulus form (unconditional). The Picard iterates are Cauchy with a *computed*
    geometric modulus (`picard_cauchy`, `N(m)=m`); the fixed point is their Cauchy
    limit (`banach_fixed_point`, located `T x*=x*` to every scale), unique
    (`banach_unique`). Completeness enters as *data + spec* (`CompleteMetricModulus`),
    not an existence miracle; the fixed point is approached by every iterate,
    reached by none. Reuses this session's own `MetricModulus`. (12 PURE.)

  - `Logic/RealEqualityWLPO` + `Logic/RealApartnessMP` — completing the **real-
    decision triad** with `RealDichotomyLLPO`: the three basic verdicts about a real
    each cost a named omniscience principle — **sign ⟺ LLPO, equality ⟺ WLPO,
    apartness ⟺ MP** — mirroring `lpo_iff_wlpo_and_mp` (LPO = WLPO ∧ MP) at the
    real level. The negation `¬cutEq x 0` is free (a decidable case-split); the
    *disjunctive* verdict (sign/equality) is LLPO/WLPO; *locating* the apartness
    witness is MP (a bounded search the located bound makes terminate). A complete
    map of where constructive analysis's real-number decisions sit. (16 + 15 PURE,
    both two-sided.)

  Together EVT + UniformLimit + Banach (force the modulus) and BW + HC + Dini +
  the real-decision triad RealDichotomyLLPO/RealEqualityWLPO/RealApartnessMP (name
  the import) answer the analysis challenge symmetrically: where classical
  analysis reaches for an axiom, 213 *either* forces the hidden modulus (EVT — the
  modulus is the theorem) *or* names and measures the import (BW — calibrated to
  LPO) — it never smuggles an exterior.

A boundary case worth keeping honest: `TauParity.doubleSum_parity` (the divisor
parity as the **fixed-point count** of the `d ↔ n/d` involution rather than a
multiplicativity table) is forcing in its *choice of form*, though the
multiplicativity route also exists — forcing and bookkeeping can co-occur, and
the claim should track which one the proof actually used.

## A primitive can be a non-constructivity *sink*

A finding from the vein-B cases above: the non-constructive content of several
*distinct* classical theorems localizes to **one** reusable primitive. The
constructive pigeonhole `Combinatorics/Pigeonhole.exists_collision` (which
*returns* the colliding pair, where the classical `no_inj_lt` only refutes
injectivity → `False`) is the single import that makes
`DividesPairPigeonhole`, `TwoSquareTheorem` (the Thue box), and `ErdosSzekeres`
(the `(inc,dec)` label box) all go through ∅-axiom. In each, the textbook proof's
sole genuinely-non-constructive step is "two of these things collide — but which?"
— and that step is exactly `exists_collision`. Once the witness-returning
pigeonhole exists, three classical theorems' "forcing" reduces to bookkeeping on
top of it. This is itself §7.1 evidence: the residue's constructive content is
*shared structure*, not per-theorem accident — the same pointing (a decidable
scan producing the witness) underwrites a whole family. The methodological lesson:
when several forcing cases share a non-constructive step, factor it into a named
primitive; the primitive, not the individual theorems, is the deliverable.

## Why the distinction is the right evidential filter

`seed/AXIOM/07_primacy.md §7.1`: "Successful derivation is the test of primacy,
not its source." But a *bookkeeping* PURE proof confirms only that the library's
axiom use was incidental — weak evidence about the residue. A *forcing* PURE
proof is the strong form: the residue reaches the result by a route classical
mathematics does not take, so the result was always residue-native. When
collecting primacy evidence, the forcing cases carry the weight.

## A corollary finding (the DIRTY-set is empty for mathematics)

A whole-corpus axiom scan (`tools/scan_all_axioms.py`) found, of ~19.6k
declarations, **no mathematical theorem that is DIRTY because the mathematics
needs a non-constructive axiom**: every real-DIRTY declaration is either a
*thesis* (`propext` = Prop-as-atom, `Quot.sound` = Lens-equality-as-`funext`)
or a tactic elaborator (`Classical.choice` inherited from Lean's `Elab` monad —
a metaprogramming boundary). So the residue already supports every *math* result
purely; genuine forcing cases are therefore **forward** — newly added classical
theorems whose textbook proof is non-constructive, re-derived ∅-axiom. That the
corpus's math contains zero "needs-an-axiom" theorems is itself a §7.1
data-point: nothing mathematical here imported an exterior.

Active running list: `research-notes/frontiers/pure_forces_different_proof.md`.
