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
- **C — non-effective → effective.** A classically non-effective existence
  forced into a *modulus / constructor*. Reveals: the rate / the construction.
  The corpus modulus programme and the `Math/Logic/` omniscience hierarchy
  (LLPO / WKL / König / Heine-Borel) are the meta-catalogue of *exactly where*
  classical logic imports — i.e. where forcing is unavoidable.

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
