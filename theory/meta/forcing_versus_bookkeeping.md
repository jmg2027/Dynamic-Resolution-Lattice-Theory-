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

A boundary case worth keeping honest: `TauParity.doubleSum_parity` (the divisor
parity as the **fixed-point count** of the `d ↔ n/d` involution rather than a
multiplicativity table) is forcing in its *choice of form*, though the
multiplicativity route also exists — forcing and bookkeeping can co-occur, and
the claim should track which one the proof actually used.

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
