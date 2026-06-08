# Cross-domain insights — the golden prime `5`: value (main) ⟷ valuation (branch)

Insights surfaced by the branch (`fibonacci_5adic_valuation`) sitting next
to main (CKM CP-phase marathon, Zolotarev/Legendre/QR,
permutation-three-readouts).  The recurring object is the prime **`5`** and
the field **`ℚ(√5) = ℚ(φ)`**.  "Proven both sides" = a shared object
already in `lean`; "bridge" = a buildable but unbuilt morphism.

## 1. `5` is the shared hinge — value vs. valuation

- **Main**: the CKM CP-phase lives on the single prime `d = NS + NT = 5`;
  the golden modulus `R_u = 1/φ²` is the *value* of `φ ∈ ℚ(√5)` (the real
  subfield of `ℚ(ζ₅)`), and `Gal(ℚ(ζ₅)/ℚ) ≅ C₄` supplies the phase.
- **Branch**: `5` is the **ramified** prime of *the same* `ℚ(√5)`
  (`disc = 5`, `x² − x − 1 ≡ (x−3)² mod 5`).  The branch reads the
  *arithmetic / 5-adic valuation* of the Fibonacci recurrence whose
  convergents converge to `φ`: rank of apparition `α(5) = 5`,
  `ν₅(F_n) = ν₅(n)` (`fibN_val_law`).

So main takes the **analytic value** `φ` of `ℚ(√5)`; the branch takes the
**p-adic structure** of the Fibonacci recurrence with the same limit.
They are two faces of one quadratic field, meeting at its ramified prime.
Same prime `5`, once as "the modulus carrier" and once as "the ramified
place."

## 2. The Cassini unit is literally shared (proven both sides)

`OrbitDimension` (the branch's `fibZ` foundation) already cites
`Mobius213.Px.PnFibonacciUniversal.det_pn_universal` (`det Qⁿ = unit`):
the Fibonacci Cassini determinant `±1` **is** the number-tower founding's
shared unit `det P = NS − NT = 1`.  Main reads this unit as `ℚ`'s
lowest-terms / the tower's conserved invariant; the branch uses the same
`±1` (`cassini_fibZ`, `fibZ_cassini_eps`) as the sign `ε = (−1)ᵐ` that
makes `fibZ_index_rec` a pure polynomial identity and drives the
quintupling.  **Already one object**, not a coincidence to be bridged.

## 3. The Legendre symbol `(5/p)` governs the rank of apparition

Main's Zolotarev/Legendre/QR machinery computes the quadratic character
`(5/p)`.  The classical rank-of-apparition law is
`α(p) ∣ p − (5/p)` — split primes (`(5/p)=1`) have `α(p) ∣ p − 1`, inert
(`(5/p)=−1`) have `α(p) ∣ p + 1`, and the **ramified** prime `5`
(`(5/p)=0`, the symbol's zero) has `α(5) = 5` — exactly the branch's
ramified signature.  The FSM file `Fib/FSMmod` already records the
split/inert period buckets per the symbol; the branch closed the
ramified `p=5` rung.

**Bridge (buildable):** prove `α(p) ∣ p − (5/p)` for general `p` from the
existing `Legendre`/QR character + a general-`p` Fibonacci FSM — unifying
the branch's `p=5` ramified case with main's `(5/p)` for the split/inert
primes under one statement.

## 4. The binary sign axis — a fourth instance

Main's `the_permutation_under_three_readouts` synthesis: `psign` =
inversion parity = `det(permMatrix)` = Legendre via Zolotarev — one
binary sign read three ways.  The branch's `ε = (−1)ᵐ` (the Cassini /
`altSign` period-2 oscillation, with `ε² = 1` collapsing the quintupling)
is the **same count-Lens binary axis** (negation = the `PairCompletion`
swap).  The companion-determinant sign already appeared as a fourth
instance in the casoratian cross-domain note; the Fibonacci Cassini sign
is the same axis read on the golden recurrence.

## 5. `disc −4` (main's CP `i`-point) vs `disc +5` (branch's golden prime)

Main's CP-phase essay selects the order-4 axis point `disc −4`
(`ℤ[i]^×=C₄`, the `i`-point) over `disc −3` (Eisenstein `C₆`).  The branch
supplies the **real-quadratic companion** `disc +5` — the *other*
fundamental discriminant, where `ℚ(√5)` is real (no roots of unity beyond
`±1`) and the structure shows up not as a root-of-unity order but as the
Fibonacci rank/valuation.  The imaginary golden prime story (`ζ₅`,
`C₄`-phase) and the real golden prime story (`√5`, Fibonacci `ν₅`) are the
two embeddings of `ℚ(√5) ⊂ ℚ(ζ₅)`.

**Bridge (open):** make explicit, in `lean`, that the `ℚ(√5)` main reads
through `ℚ(ζ₅)`'s real subfield (CP-phase) and the `ℚ(√5)` the branch
ramifies at `5` (Fibonacci) are one field object — a shared-field morphism
tying `cp_phase` to `fibonacci_5adic_valuation`.

## Status
Insights 2 and 4 are *proven shared objects* (one `lean` object each).
Insights 1, 3, 5 name **buildable bridges**: (3) the general-`p`
`α(p) ∣ p − (5/p)` rank law from the Legendre character, and (5) the
shared-`ℚ(√5)` morphism between `cp_phase` and `fibonacci_5adic_valuation`.
