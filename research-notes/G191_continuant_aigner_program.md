# G191 — The continuant / Aigner program: where modern Markov theory meets the repo, and what it can(not) close

Tier-1 synthesis after a full-arsenal sweep (4 parallel repo surveys + primary-source web research) toward
direction **(b)**: the genuine cross-node frontier of the Markov uniqueness (Frobenius 1913) conjecture.
Discipline: sourced facts separated from interpretation; "necessary" never silently upgraded to "sufficient".

## A. The decisive fact (primary-sourced): the repo already states the open conjecture exactly

The modern formulation (Rabideau–Schiffler, *Adv. Math.* 370 (2020), arXiv:1801.07155; Banaian et al.,
arXiv:2512.04026, 2025) is: there is a natural map `ℚ∩[0,1] → {Markov numbers}`, `p/q ↦ m_{p/q}`, and

> **"Frobenius' conjecture is equivalent to stating that this map is injective."** (2512.04026)

In the repo this map is `slope ↦ markovNum` (the rational `p/q` = the Stern-Brocot slope = the `List Bool`
path; `markovNum p = (mNode p).c`).  Its injectivity is exactly `Function.Injective markovNum`, and
`markovMaxUnique_iff_markovNum_injective` (`Real213/SternBrocotMarkov` §34, ∅-axiom) shows it `↔ ∀ c≥5,
MarkovMaxUnique c`.  **So the repo's §34 iff is the modern statement of Frobenius verbatim.**  Confirmed
open as of 2026 — no claim of resolution in either source.

## B. What modern math actually proves — and its ceiling (necessary, not sufficient)

Aigner's three monotonicity conjectures (from *Markov's theorem and 100 years of the uniqueness
conjecture*), with `1 ≤ p < q`, `gcd(p,q)=1`:

  1. **Fixed Numerator**: `q < q'`, `gcd(p,q')=1` ⟹ `m_{p/q} < m_{p/q'}`.
  2. **Fixed Denominator**: `p < p' < q`, `gcd(p',q)=1` ⟹ `m_{p/q} < m_{p'/q}`.
  3. **Fixed Sum**: `0 < i < p`, `gcd(p−i,q+i)=1` ⟹ `m_{p/q} < m_{(p−i)/(q+i)}`.

**Proven**: Lee–Li–Rabideau–Schiffler (continued fractions / continuants); Greg McShane gave a unified
proof via hyperbolic geometry and the **stable norm**.  **Status vs. Frobenius** (sourced):

> "If [uniqueness] is true, then we recover a total order … Aigner provided a triple of conjectures …
> predicting features of this total ordering." (2512.04026)

i.e. the three orderings are **necessary consequences of uniqueness, not sufficient to establish it**.
They constrain *where collisions could sit* (the slopes are ordered) but never exclude *that two slopes
share a value* — which is injectivity.  **So even the full modern apparatus does not close `H`.**  This
is the corrected, load-bearing reading: (b) is the only direction toward the kernel, and it does **not**
arrive there even with everything known.

## C. The technical core is the continuant (Frobenius 1913)

All three orderings reduce to **continuant** inequalities.  The mechanism: `m_{p/q} = K(CF-shape of
p/q)`, where `K[a₁,…,aₙ]` is the Euler continuant (numerator of `[a₁;…,aₙ]`, = the `(1,1)`-entry of
`∏[[aᵢ,1],[1,0]]`), and the CF-shape comes from the Christoffel word of `p/q` (a fence-poset /
snake-graph order-ideal sum in the cluster-algebra picture).  Increasing `q` (fixed `p`) appends/raises a
partial quotient; continuant monotonicity gives the ordering.

## D. Repo arsenal — what is in hand vs. missing (4-survey map)

**In hand (∅-axiom):** `Mat2` SL₂(ℤ) + traces + discriminant (`HyperbolicEllipticTrace`); the
Stern-Brocot **continuant matrices** `mInterval`/`mNode` with `det = 1`, `mInterval_markov` (the Markov
equation on the tree), Vieta recurrences `markoff_vieta(_trace)(_R)`; the **Cohn matrix** `C² ≡ −I (mod
c)` along every path (`cohn_sq_neg_one_mod`); the slope machinery + `slope_path_inj` (slope injective);
Cassini/`farey_neighbour`; the CF-FSM `cfStep/cfCoeff/cfExpansion` (Euclidean digits); Stern-Brocot
adjacency `sbInterval_adj` + `sbInterval_mediant_coprime`; Vandermonde-2 mediant splits.

**Missing — the Aigner core:**
  - **The isolated continuant `K[a₁..aₙ]` recurrence + monotonicity** — was only *implicit* in `mInterval`.
    **Now built** (`Real213/Continuant.lean`, ∅-axiom, this round): `continuant`/`contPair`,
    `continuant_cons2` (Euler recurrence, `rfl`), `one_le_continuant`, `continuant_head_strict_mono`,
    `continuant_lt_prepend`.  This is the technical-core tool of the proven orderings.
  - **The Frobenius continuant formula** `markovNum p = K(CF-shape of slope p)` — the bridge from the
    `mInterval` matrix-product entry to the continuant of the CF of the Christoffel word.  **Unbuilt; the
    substantial step.**  Needs: path `List Bool` → Christoffel word → CF partial-quotients → continuant,
    and an identity matching that continuant to `(mNode p).c`.
  - **Cluster algebra / snake graph / perfect matching / frieze** — *entirely absent* (survey C); the
    cluster-algebraic route (LLRS) would be from scratch.  The continuant/CF route is the cheaper one.

## E. The honest program for (b), in order

  1. ✅ **Continuant primitive + monotonicity** (`Real213/Continuant.lean`) — done, ∅-axiom.
  2. ✅ **Continuant ↔ matrix-product entry**: `K[a₁..aₙ] = (∏[[aᵢ,1],[1,0]]).(1,1)`
     (`contMatProd_eq`, `continuant_eq_contMatProd`, ∅-axiom) — the continuant now lives inside the repo's
     `Mat2` algebra (the same `mul` carrying `genL`/`genR`/`mInterval`).
  3. **Path → CF partial quotients**: extract the run-length (Christoffel) encoding of `p : List Bool`
     and relate the `genL/genR` product to the `[[aᵢ,1],[1,0]]` product.  Medium; the genL/genR basis is
     not the `[[a,1],[1,0]]` basis, so a conjugation/normalisation is needed.
  4. **Frobenius formula** `markovNum p = K(shape p)` — the bridge (D, substantial).
  5. **One Aigner ordering** (e.g. Fixed Numerator `p=1` first — the single-spine case, likely already
     near `markovNum_lt_append`; then general `p`) as the first genuine **cross-node** ∅-axiom Markov
     ordering theorem.  Necessary-not-sufficient for `H`, but real new frontier content.

**Ceiling, restated.**  Completing E1–E5 would land Aigner monotonicity in ∅-axiom — a real result, the
first cross-node Markov ordering in the repo — but **not** the conjecture.  The kernel
`OrbitRealizabilityH` (which ℤ-lift of a mod-`c` `√(−1)` residue is *realised* — the passing pattern)
is orthogonal to the slope-ordering and remains the open core.  No surveyed domain, and no modern
technique, supplies it.

### Pointers
- repo conjecture statement: `Real213/SternBrocotMarkov` §34 `markovMaxUnique_iff_markovNum_injective`
- new tool: `Real213/Continuant.lean`
- arsenal: `HyperbolicEllipticTrace` (trace), `MarkovUniqueness` §9 (`cohn_sq_neg_one_mod`), `SternBrocotMarkov` (`mInterval`, `slope_path_inj`, `mInterval_markov`), `DyadicFSM/ContinuedFraction` (`cfCoeff`)
- kernel: `OrbitRealizabilityH`, `markovMaxUnique_iff_orbitRealizabilityH`; passing-pattern prose in `theory/math/analysis/markov_uniqueness.md`
- sources: Rabideau–Schiffler arXiv:1801.07155 (*Adv. Math.* 370, 2020); Banaian et al. arXiv:2512.04026 (2025); McShane (stable-norm unified proof of Aigner)
