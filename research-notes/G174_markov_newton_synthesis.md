# G174 — Markov uniqueness ↔ the Newton / Casoratian / FSM frameworks (idea-level graft)

**Tier 1 (volatile).**  After merging `main` (NewtonGregory, FiniteDepthAlgebra, CasoratianSigned,
StateMachine FSM, ℤ-difference-Lens), this note records the *conceptual* — not merely tactical —
points where that work touches the Markov uniqueness arc (`G173`,
`Real213/MarkovUniqueness` + `ModArith/MarkovPrimeFactor`).  One concrete anchor is proven
(`fib_spine_recurrence`); the rest are framings, the most useful being the Myhill–Nerode reading
of the open crux.

## A — the Markov spine sits in the C-finite (not poly-depth) layer  [PROVEN]

The golden Markov spine — odd-index Fibonacci `1,2,5,13,34,89,…` — satisfies the **trace-`NS`
linear recurrence**

  `fib(2n+1) + fib(2n+5) = 3·fib(2n+3)`   (`fib_spine_recurrence`, ∅-axiom via `ring_nat`),

i.e. `fib(2n+5) = 3·fib(2n+3) − fib(2n+1)`, characteristic polynomial `x²−3x+1`.  This is the
**characteristic polynomial of the golden matrix `P=[[2,1],[1,1]]`** (trace `3 = NS`, det `1`),
whose `P`-orbit is the odd-index Fibonacci sequence; the recurrence step is literally the
**Markov-Vieta jump** on the spine (`F_{2n−1}+F_{2n+3}=3F_{2n+1}`).  The Pell (silver) spine is
the analogue with coefficient `6` (char poly `x²−6x+1`, trace of the silver square / Cohn `B`).

Placement in `main`'s hierarchy (`cf_holonomicity_hierarchy`, `NewtonGregory`): the spine is
**C-finite** (constant-coefficient linear recurrence) but grows exponentially, so it has *infinite
forward-difference depth* — it is **not** Newton-reconstructible / not `polyDepthZ`-finite, exactly
like the geometric witness `2ⁿ` (`QuasiPolyCF ⊊ C-finite ⊊ holonomic`).  `FiniteDepthAlgebra`'s
`periodic_finite_depth_const` (finite-depth + periodic ⟹ constant) confirms the boundary from the
other side: the Markov/quadratic-irrational sector and the Newton-reconstructible sector meet only
at the constants — the Markov spine is genuinely outside the polynomial-depth world.

So `NS = 3` is one number wearing four hats: the Markov coefficient (`x²+y²+z²=3xyz`), the trace of
`P`, the spine recurrence coefficient, and the simplex count `NS`.

## B — the `√(−1)` residue *is* the Casoratian (Cassini) of the spine recurrence  [PROVEN]

`fib_spine_sqrt_neg_one`: `fib(2n+2)² + 1 = fib(2n+1)·fib(2n+3)`.  Read in `main`'s language this
is precisely the **Casoratian** (discrete Wronskian) of the second-order recurrence above: the
cross-determinant `fib(2n+1)fib(2n+3) − fib(2n+2)²` of two consecutive solution windows, which the
Cassini/Catalan identity pins to the constant `−1`.  `main`'s `CasoratianSigned` ("the residue
floor is the depth-0 signed Casoratian") is the general frame; the Markov `√(−1)` encoding is its
number-theoretic shadow: **the constant Casoratian `±1` of the spine, reduced mod the spine's
Markov number, is the square root of `−1`** that indexes that number.  The chain
`Casoratian = Cassini = √(−1) residue = Gaussian i = order-4 generator S` (`cohn_sq_neg_one_mod`,
`C²≡−I`) is one object seen at the recurrence / number-theory / matrix levels.

## C — uniqueness = Myhill–Nerode minimality of the Markov tree coalgebra  [FRAMING of the open crux]

The cleanest idea-level graft of `main`'s **StateMachine / FSM Lens** work.  The Markov tree is a
coalgebra (each triple has Vieta children — `MarkovReachable`); the map `triple ↦ max` labels
states by a number, and `max ↦ √(−1)-residue u = a·b⁻¹ (mod max)` is an **observable / trace**.
In FSM terms:

  **Markov uniqueness ⟺ the Markov tree, labelled by its maximum, is *reduced* (minimal):
  distinct ordered triples (states) have distinct labels — equivalently, the residue/trace map
  separates states.**

This is the exact shape of `main`'s `traceEq_finite_minimal` / `mu_carrier_reachable_reduced_machine`
(reachable + deterministic + reduced; trace map injective).  The arc already supplies
*reachable* (`markov_reachable_*`) and *deterministic* (Vieta children well-defined); **uniqueness
is the missing *reduced*.**

What this framing *buys* (beyond analogy): it pinpoints the obstruction.  The reduction
"`#{x:x²≡−1 mod c} ≤ 2 ⟹ c unique`" says the residue trace separates states **when the observable
has ≤2 values** (prime powers, `two_roots_of_prime_pow`).  At composite `c` with ≥2 prime factors
the observable takes ≥4 values and **stops separating** — the FSM is *not* reduced by this trace
alone (several triples could share a residue).  So the open zone is exactly "the `√(−1)`-residue
is an insufficient observable for Myhill–Nerode at composite `c`"; closing C6 = finding the trace
(or proving this one suffices) that makes the Markov tree reduced.  This is a sharper statement of
the residue-map-injectivity crux than "it's hard", and it is `main`'s minimality vocabulary
applied verbatim.

## D — the Vieta jump as a difference; ℤ-as-difference-Lens  [FRAMING]

`main` grounds `ℤ` as the difference-Lens (a `ℕ`-pair `(m,n)↦m−n`).  The Markov Vieta involution
`c ↦ c' = 3ab − c` is a **difference** (a reflection `c+c' = 3ab`), and the neighbor invariant
`a²+b² = c·c'` (`markov_xy`) is the product of the two roots of `t² − 3ab·t + (a²+b²)`.  The whole
tree is generated by this one difference-Lens reflection; the `√(−1)` lives in `ℤ[i]`, the
order-4 axis of the difference-Lens readout group (`ImaginaryQuadraticUnitTrichotomy`,
`spiral_coordinate`).  Not formalized here; a candidate for sharpening the "Vieta = signed
difference" reading against `06_lens_readings.md` §6.7.

## What is proven vs. framing

- **A, B** — proven ∅-axiom (`fib_spine_recurrence`, `fib_spine_sqrt_neg_one`,
  `cohn_sq_neg_one_mod`).  Concrete bridges: spine = trace-`NS` C-finite recurrence; its Casoratian
  = the `√(−1)` residue.
- **C** — a framing that re-states the open C6 crux in `main`'s Myhill–Nerode vocabulary and
  *localizes the obstruction* (insufficient observable at composite `c`).  Not a proof; does not
  claim injectivity (per the red-team standing warning).
- **D** — a framing / future sharpening.

## Next (idea-driven)

- Express `MarkovReachable` as an actual coalgebra and the residue as an `Observable`, then state
  "reduced at `c`" and *prove it equals `MarkovMaxUnique c`* (a clean equivalence, no new math) —
  this would make C as formal as a definition-unfolding, isolating the open content to the
  observable-separation lemma.  Guard against vacuity.
- Pell-spine recurrence `pell(2n+1)+pell(2n+5)=6·pell(2n+3)` (silver, coeff `6`) — the second
  C-finite Markov spine; same Casoratian story with the silver Cassini.
