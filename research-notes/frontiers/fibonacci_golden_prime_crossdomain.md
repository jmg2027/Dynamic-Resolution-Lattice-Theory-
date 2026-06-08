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

**Bridge (CLOSED):** `α(p) ∣ p − (5/p)` built for general `p` from the
`Legendre` character + the universal Fibonacci-mod-`p` machinery
(`DyadicFSM/RankApparition.lean`, 10 PURE).  `rankIndex p hp = p − (5/p)` is
dispatched on the FSM-walking character `legendre213 5 p` (split `p−1`, inert
`p+1`, ramified `p`), and `rank_law_dispatch` gives `p ∣ F_{p−(5/p)}` — each
case discharged through the actual universal theorem for its branch (split via
the `𝔽_p` Binet/FLT bridge `binet_F_p_minus_1_zero`, inert via the `𝔽_{p²}`
Frobenius FLT `fpp1_eq_zero_of_frob_phi`, ramified `p=5` via
`rank_apparition_five`).  Mirrors `UniversalDispatch.universal_dispatch_pellCoeff`
(period dispatch); here the read-out is the entry point.

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

**Bridge (CLOSED):** the shared-field morphism is built in
`lean/E213/Lib/Math/NumberTheory/GoldenFieldBridge.lean` (10 PURE).  The Binet
polynomial `x²−x−1` (Fibonacci `ℚ(√5)`, `FibApparitionMod5`) and the
Gaussian-period polynomial `x²+x−1` (`ℚ(ζ₅)⁺`, `CyclotomicFive`/`cp_phase`) are
one object under `x ↦ −x` (`bPoly_neg_eq_gPoly`: `bPoly(−x) = gPoly x`), share
discriminant `5`, and ramify at the single prime `5` — each a perfect square
mod `5` (double roots `3`, `2`; negatives, `3+2≡0`).  `shared_golden_field_morphism`
bundles the morphism, the shared discriminant, both ramifications, the
Fibonacci `α(5)=5` signature (`rank_apparition_five`), and the cyclotomic
golden subfield (`golden_real_subfield`).

## Status
Insights 2 and 4 are *proven shared objects* (one `lean` object each).
Insights **3 and 5 are now CLOSED**: (3) the general-`p` `α(p) ∣ p − (5/p)`
rank law from the Legendre character (`DyadicFSM/RankApparition.lean`), and (5)
the shared-`ℚ(√5)` morphism between `cp_phase` and `fibonacci_5adic_valuation`
(`NumberTheory/GoldenFieldBridge.lean`).  Insight 1 (value vs. valuation hinge)
remains a conceptual framing, not a single unbuilt morphism.

## Remaining open direction — higher valuation rungs for general `p`

The rank law `α(p) ∣ p − (5/p)` is the **entry-point** (`νₚ ≥ 1`) rung,
Legendre-dispatched.  The all-orders lift is open for general `p`: at the
ramified `p = 5` the quintupling identity `F_{5m} = F_m·(25F_m⁴+25(−1)ᵐF_m²+5)`
(`fibZ_quintuple`) supplies one factor of `5` per quintupling, closing
`ν₅(F_n) = ν₅(n)` (`fibN_val_law`).  The general statement
`νₚ(F_n) = νₚ(α(p)·k) = νₚ(k) + νₚ(α(p))`-style lift needs the `p`-tupling
analogue (an index-`α(p)`-multiplication identity with a cofactor `≡ 1 mod p`)
— buildable from `fibZ_index_rec` iterated to `k = α(p)`, parametric in the
rank.  Only `p = 5` is carried out.

## New branch×main insights from this session's closures

Surfaced by the rank law (`RankApparition`) + the `ℚ(√5)` morphism
(`GoldenFieldBridge`) sitting next to main's Zolotarev / Pisano-predictor /
CP-essay arcs.  The recurring object is the Legendre symbol `(5/p)`.

### 6. The rank-law character `legendre213 5 p` IS Zolotarev's permutation sign

This branch's rank law dispatches on `legendre213 5 p` — `(5/p)` read as the
**terminal state of the FSM trajectory** `x ↦ 5x mod p` walked `(p−1)/2` steps
(Euler's criterion).  Main's `ZolotarevMuBridge.zolotarev_mu` proves `(a/p) =
psign σ_a` — `(5/p)` read as the **parity of the `×5 mod p` permutation**.  So
the *same* `(5/p)` that fixes the Fibonacci rank `α(p) ∣ p − (5/p)` is the sign
of the `×5` permutation: the Fibonacci entry point is governed by a permutation
parity.  **Bridge (buildable):** `legendre213 5 p = (if psign σ_5 = 1 then 1
else 2)` (the FSM-walk Legendre = the Zolotarev permutation sign, modulo the
ramified `=0` corner) — then `α(p) ∣ p − psign(σ_5)`, tying the rank dispatch
to the Zolotarev converse.  A **fifth** "permutation under three readouts"
instance: `(5/p)` = trajectory terminal = permutation sign = `det(permMatrix)`,
now also = Fibonacci rank offset.

### 7. Rank dispatch and Pisano-period dispatch are one character, two read-outs

Main's `UniversalDispatch.universal_dispatch_pellCoeff` dispatches the Pisano
**period** `π(p)` (the order of the Pell matrix) on `legendre213 5 p`; this
branch's `rank_law_dispatch` dispatches the **entry point** `α(p)` on the same
character.  Period and rank are the two canonical Fibonacci-mod-`p` invariants,
and `α(p) ∣ π(p)` (the first zero divides the cycle length).  One Legendre
character, two FSM read-outs — first-zero (rank) vs cycle-length (period) — each
with its own dispatch theorem of identical shape (`fin3_cases` on the symbol).
The branch supplies the entry-point face of a dispatch main had only for the
period.

### 8. The `x ↦ −x` morphism vs. main's `σ²` conjugation on `ℚ(√5)`

`GoldenFieldBridge`'s `x ↦ −x` relates the two *generators* of `ℚ(√5)` (the
Binet `x²−x−1` and the cyclotomic-period `x²+x−1`), the disc-`+5` real face.
Main's `CyclotomicFive` carries `σ² =` complex conjugation, the order-2 element
of `Gal(ℚ(ζ₅)/ℚ) ≅ C₄` that *fixes* `ℚ(√5)` and swaps the periods `η₀ ↔ η₁`.
Distinct order-2 maps on the same field — generator-negation (branch) vs
period-swap / Galois conjugation (main) — both witnessing that `ℚ(√5)` is the
order-2 real subfield where the imaginary CP story (disc `−4`) and the real
Fibonacci story (disc `+5`) are the two embeddings `ℚ(√5) ⊂ ℚ(ζ₅)`.
