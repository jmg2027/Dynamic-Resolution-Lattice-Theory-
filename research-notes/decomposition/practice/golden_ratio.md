# Decomposition: the golden ratio φ / continued fractions ([1;1,1,…])

*213-decomposition of φ and the continued fraction, per `../README.md`.*
*Cross-links `cardinality.md` (the diagonal residue — also self-application) and
`derivative.md` (the limit as a reading's residue, computed via a modulus).*

## The decomposition

- **Construction `C`** — the **self-applying distinguishing iteration**. Start with a
  pair `(p, q)` (a directed count, the difference-Lens carrier of `integers.md`) and apply
  the *same* act again: `T(p, q) = (2p + q, p + q)`. This is `C`'s own re-entry — the
  distinguishing whose next operand is its own output, the Möbius matrix `P = [[2,1],[1,1]]`
  iterated. In 213 the iterator is read straight off the residue's self-pointing
  (`seed/AXIOM/05_no_exterior.md` §5.6: `P(x) = (2x+1)/(x+1)`, "the minimum fixed point of
  self-reference"), not a structure added — it is a ∅-axiom theorem. The continued fraction
  `[1;1,1,1,…]` is the *same* `C` written as nested re-entry: every partial quotient is `1`,
  i.e. the iteration applied with no new input.
- **Reading `L_ratio`** — the **ratio-reading at limit resolution**. Project each iterate
  `(p_n, q_n)` to its ratio `p_n / q_n` — the convergent — and read this ratio at the
  *residue* resolution (the `derivative.md` parameter): not "adjacent at step 1" but
  "adjacent via a modulus, the bracket shrinking." The finite generator is the recurrence
  `s(n+2) = 3·s(n+1) − s(n)` (the trajectory) plus the **honest modulus** `N(m,k) = 2k`
  (how deep to iterate for precision `k`). The limit is never the operand; the modulus is.
- **Residue** — what `L_ratio` forces but cannot capture: **φ itself**. The convergents
  climb toward φ and *never land on it* — each sits exactly the Cassini step `+1` off the
  frozen relation `a² = a·b + b²`. φ is the reached-by-none limit of the self-applying
  iteration, named by a finite signature (recurrence + modulus), never grasped as an object
  inside `Nat`. **A fixed point IS a residue**: `P(φ) = φ` is the frozen reading of the
  same surplus the dynamic convergents only approach.

## Re-seeing

```
   "(p,q)"            =  ⟨ directed count-pair | — ⟩                  (C, before any reading)
   convergent p_n/q_n =  ⟨ T^n(seed) | L_ratio ⟩  (discrete res.)    fib(2n+2)/fib(2n+1)
   φ                  =  Residue(L_ratio, C)                         the frozen fixed point
   "P(φ) = φ"         =  P(⟨ self-applying T | L_ratio ⟩) at limit res.  reach-by-none limit
   [1;1,1,…]          =  the SAME C as nested re-entry (every aₙ = 1)
```

So the continued fraction `[1;1,1,…]` is the **construction** (alternating distinguishing,
each step re-feeding the act), and φ is its **residue** under the limit-resolution ratio
reading — exactly as `derivative.md`'s `f'` is the residue of the difference-quotient
reading. The convergents `fib(2n+2)/fib(2n+1)` are `C` read at discrete resolution; φ is
the same `(C, L)` read in the residue, computed by the modulus `N(m,k) = 2k`, the limit
itself never an operand.

## Revelation (residue-surfaced + collapse)

φ is **not an object** — it is the **residue of the self-applying distinguishing iteration**,
the reached-by-none fixed point of `C`'s own re-entry. This surfaces a residue (the
README's third Revelation kind) and collapses several apparently-distinct things into one
`(C, L)` read out at different scales:

1. The dynamic convergents (Pell/Fibonacci ratios) and the frozen fixed point are **one
   object, two readings** of the same residue — `P(φ)=φ` (frozen) and `Pⁿ → φ` (dynamic)
   are §5.7's simultaneous readings, not two facts. Verified shadow: the convergents lie
   below φ and *never* satisfy the homogeneous frozen relation
   (`dynamic_approaches_never_reaches_frozen`) — reached-by-none, the literal
   `object1_not_surjective` signature applied to a *converging* iteration.
2. The conserved unit `det Pⁿ = 1 = NS − NT` (the Cassini surplus, the residue's signature)
   is the **same** unit read across algebra, analysis, and atomicity
   (`residue_unit_three_scales`) — the `+1` that separates dynamic from frozen φ at every
   layer is the orbit's conserved determinant.
3. The continued-fraction determinant is **universally a unit** for *any* real
   (`cf_det_sq`: `Wₙ² = 1`), with φ's all-`1`s CF as one instance (`cfQn_fib`: the all-1s
   partial quotients give Fibonacci denominators). So "φ is special" collapses to "φ is the
   `aₙ ≡ 1` instance of the one unimodular CF law" — the deepest re-entry (slowest-shrinking
   residue), not a separate kind of number.

That φ recurs across unrelated domains (Cayley–Dickson Moufang-failure `1 − ½·(1/φ)^rank`,
the CKM phase's `π/φ²`, neutrino mass ratios — §5.6) is therefore **one fixed point read
out**, not a coincidence needing reconciliation: the same residue, the matrix's fixed point,
surfacing wherever a self-applying distinguishing is read at limit resolution. This is
CLAUDE.md's "Limit/infinity deified" failure stated positively — φ is the *shape* of the
ratio-reading's residue (finite signature: recurrence + modulus + the conserved `+1`), not
a transcendent attractor above the finite.

## Lean grounding — verified anchors (file:theorem)

All cited declarations grep-verified to exist; docstrings assert ∅-axiom (PURE). The
purity claim rests on the in-file docstrings — `tools/scan_axioms.py` was not re-run here.

**The iterator IS the self-applying construction (φ = its residue, concept):**
- `seed/AXIOM/05_no_exterior.md` §5.6 — the Möbius iterator `P(x) = (2x+1)/(x+1)`, φ as
  "the minimum fixed point of self-reference"; §5.7 — frozen `P(φ)=φ` vs dynamic `Pⁿ→φ` as
  simultaneous readings of one residue. The *concept* anchor.
- `Lib/Math/Algebra/Mobius213/Px/MobiusSelfForm.lean:119` `mobius_iteration_master` — `T`
  maps convergent `n` to convergent `n+1` (the iteration in pure integer arithmetic; "the
  fixed-point iteration `Tⁿ(0/1) → φ` expressed in integers"). `:263`
  `self_reconstruction_master` — P is a fixed point of its own describe-reconstruct cycle
  (the construction re-entering itself).
- `Lib/Math/Algebra/Mobius213.lean:244` `mobius_213_pell_unit_invariant_forall` — the
  conserved orbit unit `= −1` ∀n (the symplectic invariant of the iteration); `:178`
  `mobius_213_pell_unit_invariant` (8-layer witness).

**φ is the reached-by-none residue (the hypothesis, certified as the `Nat` shadow):**
- `Lib/Math/NumberSystems/Real213/Phi/FibCassiniNat.lean:183`
  `dynamic_approaches_never_reaches_frozen` — convergents lie below φ, satisfy the Cassini
  form `a²+1 = a·b+b²`, and *never* satisfy the frozen `a² = a·b+b²`. The literal
  "approaches but never reaches" — φ reached-by-none. `:167` `convergent_never_frozen`,
  `:128` `fib_convergent_below_phi`, `:62` `fib_cassini_norm`.
- `Lib/Math/NumberSystems/Real213/Phi/PhiCauchyLimit.lean:66` `phiCauchy_limit_eq_phiCut` —
  φ built **as the limit** of the convergent Cauchy sequence (modulus `N(m,k)=2k`) equals
  the closed-form `phiCut` on the nose; `:46` `phiConvergentSeq` (the modulus-carrying
  Cauchy sequence). The residue computed via a finite generator, not grasped.

**The conserved unit / collapse across scales:**
- `Lib/Math/Analysis/Cauchy/PhiResidueGlue.lean:61` `residue_unit_three_scales` —
  `det Pⁿ = Wₙ = NS−NT = 1` (algebra/analysis/atomicity one unit); `:38` `orbit_det_is_glue`
  (the load-bearing arrow `det Pⁿ = NS−NT`).
- `Lib/Math/Algebra/CassiniUnimodular.lean:123` `det_step`, `:142` `det_closed`
  (`det s n = qⁿ·det s 0`), `:163` `cassini_law_one_at_two_multipliers` — the golden `q=1`
  (conserved) vs swap `q=−1` (alternating) as one parametric law at two unimodular
  multipliers; `:60` `det_golden`, `:68` `det_period2_alternates`.
- `Lib/Math/NumberSystems/Real213/ContinuedFraction/ContinuedFractionFloor.lean:104`
  `cf_det_sq` — the CF cross-determinant is universally a unit (`Wₙ²=1`) for *any* real,
  φ's all-1s CF the one instance; `:87` `cf_det_step` (`W_{n+1} = −Wₙ`), `:140` `cfQn_fib`
  (all-1s partial quotients → Fibonacci denominators).

**Dropped citations (named in the brief, not used):** `SpiralRotationInvariant` — searched,
no such theorem; the spiral/rotation content is not load-bearing for the residue claim, so
omitted rather than forced. `CassiniUnimodular.det_step` was *kept* (verified at `:123`).

## Note for the technique — Residue stratifies into **escaping** vs **converging**

This decomposition answers a shape-question the README's "Residue is first-class, and
stratifies" left half-open, and sharpens it against `cardinality.md`.

**Does this confirm Residue = self-application limit?** Yes, and it shows the *form* of the
self-application matters. Both `cardinality.md` and this file have `C` re-entering itself:

| | `cardinality.md` (diagonal) | `golden_ratio.md` (fixed point) |
|---|---|---|
| self-application | `g x := t(f x x)` (cover re-entering) | `Tⁿ(x)`, the iterator re-feeding its output |
| Lean engine | `OneDiagonal.lawvere_fixed_point` | `mobius_iteration_master` / `self_reconstruction_master` |
| residue behaviour | **escapes** — `t = not`, no fixed point, surplus outside every row (`object1_not_surjective`) | **converges** — `t` *has* a fixed point φ, the iteration asymptotes to it (`dynamic_approaches_never_reaches_frozen`) |
| reached-by-none | yes (no row lists the diagonal) | yes (no convergent lands on φ) |

So **a fixed point is always the residue of a self-applying reading** — but Residue
**stratifies by the self-map's fixed-point structure**, and this is *the same dichotomy
already in the Lean*. `cardinality.md`'s engine is `no_surjection_of_fixedpointfree`: the
diagonal escapes **precisely because `t = not` is fixed-point-free** (`05_no_exterior.md`'s
"Bool-style, liar-like, oscillation not convergence"). φ converges **precisely because its
`t` has a fixed point** (Nat-style, Lambek-like, "the iteration reaches its limit and stays
there"). The split escaping-vs-converging is therefore not two kinds of residue but **one
residue read through `t`'s fixed-point structure** — and 213 already names it: it is the
`q = −1` (swap, alternating, fixed-point-free → escapes) vs `q = +1` (golden, conserved,
fixed point → converges) of `cassini_law_one_at_two_multipliers`. The diagonal residue and
the φ residue are the **two unimodular multipliers of the one self-application law**. The
README's normal form `⟨C | L⟩ ⊕ Residue(L,C)` should carry, on the Residue, a **multiplier
bit** `q = ±1` — `q=−1` (escaping/oscillating, Cantor's diagonal, the liar) vs `q=+1`
(converging/conserved, φ, Lambek closure) — the single parameter that decides whether the
reached-by-none surplus oscillates outside every reading or asymptotes to a fixed point the
modulus narrows but never reaches.
