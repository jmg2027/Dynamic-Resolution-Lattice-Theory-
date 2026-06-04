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

**The phantom-root filter [now PROVEN at the testbed].**  `markov_phantom_root_filter` snipes the
C6 barrier at the *first* composite `c = 65 = 5·13` (`ω=2`, the `2^ω = 4` root explosion
`{8,18,47,57}` = two `±` pairs): the `u²≡−1` observable over-counts (`not_sqrtNegOneTwoRoots_65`),
**yet `markovEq · · 65` admits no triple** — every root is *phantom*.  The extra observer that
separates is the primitive Diophantine descent constraint `markovEq` itself: even where the
descent quotient `(u²+1)/65 ∈ {1,5,34,50}` is a Markov number (`1,5,34`), no triple closes because
`65` is not on the tree.  So the residue observable is provably insufficient and the descent
constraint provably filters — at `65`, exactly the Myhill–Nerode "extra observer" the framing
calls for.  (Advanced to the *real* composite Markov number `1325 = 5²·53` below — `markov_composite_separation`.)

## D — the Vieta jump as a difference reflection; the depth boundary  [PROVEN]

`main` grounds `ℤ` as the difference-Lens (a `ℕ`-pair `(m,n)↦m−n`).  The Markov Vieta involution
`c ↦ c' = 3ab − c` is exactly a **difference reflection**: `vieta_reflection` proves `c + c' = 3ab`
(reflection about `3ab`) and `3ab − c' = c` (involution).  So the discrete tree transition *is* a
structural additive reflection on the state — the difference-Lens shadow of `t ↦ 3ab − t`; the
neighbor invariant `a²+b² = c·c'` (`markov_xy`) is the product of the two roots of
`t² − 3ab·t + (a²+b²)`.

**Depth-boundary alignment with `main`'s holonomic marker.**  `main`'s marker is
`polyDepth d ⟹ Δ^{d+1} = 0` (finite forward-difference depth = annihilated by a *pure* power of
`Δ`).  The golden spine `g(n) = fib(2n+1)` satisfies `g(n+2) − 3g(n+1) + g(n) = 0`
(`fib_spine_recurrence`), i.e. it is annihilated by the shift operator `E² − 3E + 1`; rewriting in
`Δ = E − 1` gives the annihilator **`Δ² − Δ − 1`** — *the golden ratio's minimal polynomial*.  Its
**nonzero constant term `−1`** is the precise reason the spine is **strictly C-finite, not
poly-depth**: a pure `Δ^k` annihilator (poly-depth) has no such term.  This is the exact
alignment of the infinite-forward-difference-depth boundary with `main`'s `cf_holonomicity`
markers (`QuasiPolyCF ⊊ C-finite`): the Markov spine sits just past the polynomial layer, its
difference-annihilator being the golden quadratic.

## What is proven vs. framing

- **A, B, D** — proven ∅-axiom (`fib_spine_recurrence`, `pell_spine_recurrence`,
  `fib_spine_sqrt_neg_one`, `cohn_sq_neg_one_mod`, `vieta_reflection`).  Spine = trace-`NS`
  C-finite recurrence with golden difference-annihilator `Δ²−Δ−1`; Casoratian = the `√(−1)`
  residue; Vieta jump = difference reflection/involution.
- **C** — the Myhill–Nerode reframing of the open C6 crux; the **phantom-root filter**
  (`markov_phantom_root_filter`, `65`) and **`markov_composite_separation`** (the *first real*
  composite Markov number `1325=5²·53`: `markovEq` separates the 4 roots into the valid pair
  `{507,818}` recovering `(13,34,1325)` and the phantom pair `{182,1143}` closing no triple — so
  uniqueness holds at `1325` structurally) are *proven* instances of the "extra observer".  Still
  not the *general* residue-injectivity at all composite `c` (per the red-team warning) — that is
  the continuation; but the mechanism is now demonstrated at a genuine composite Markov number.
- **Prime-power input** — `sqrtNegOneTwoRoots_prime_pow` promotes `SqrtNegOneTwoRoots (p^(k+1))`
  to a named theorem (the Button/Zhang `≤2`-roots, via the `p`-adic valuation split
  `two_roots_of_prime_pow`).

## Next (idea-driven)

- Express `MarkovReachable` as an actual coalgebra and the residue as an `Observable`, then state
  "reduced at `c`" and *prove it equals `MarkovMaxUnique c`* (a clean equivalence, no new math) —
  this would make C as formal as a definition-unfolding, isolating the open content to the
  observable-separation lemma.  Guard against vacuity.
- Pell-spine recurrence `pell(2n+1)+pell(2n+5)=6·pell(2n+3)` (silver, coeff `6`) — the second
  C-finite Markov spine; same Casoratian story with the silver Cassini.
