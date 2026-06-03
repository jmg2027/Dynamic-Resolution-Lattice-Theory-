# G188 — depth/order duality = the founding invert-twin at the sequence scale

**Tier 1 (volatile), research memo.**  The deep synthesis tying the whole non-holonomicity /
discriminant / number-tower-founding arc into one structure, developed while three specialist
agents fan out on (a) the order-`k` Casoratian + cubic discriminant, (b) the π reduction + the
bounded-P-recursive core, (c) the unified residue ceiling.  This memo is the orchestrator's
synthesis; concrete agent results get folded in as they land.

## The two independent finiteness measures

A sequence carries **two** orthogonal "finite generation" counts:

  - **depth** (the *additive* fold): the number of forward differences `Δ` until the result is
    constant.  `DepthCharacterization.finite_depthZ_iff` — *finite depth `d` ⟺ degree-`≤d`
    polynomial* (Newton basis).  So **finite depth = polynomial**.
  - **order** (the *multiplicative* fold): the dimension of the linear span of the orbit
    `{shift^i s}` — equivalently the least `k` with a length-`k` linear recurrence.  Detected by
    the **Casoratian** (discrete Wronskian): order `≤ k` ⟺ the `k×k` Casorati determinant of the
    shifts degenerates / is conserved with a determinant-multiplier (`CasoratianStep.casoratian_step`,
    `SecondCasoratian.second_casoratian`).

These are genuinely independent, and the ladder is exactly their interleaving:

```
finite depth          = polynomial            (Δ closes to a constant)
   ⊊
finite order, const-coeff = C-finite          (orbit spans finite dim; 2ⁿ, Fib, periodic)
   ⊊
finite order, poly-coeff  = P-recursive       (HomogRec; n!, ζ-recurrences)
   ⊊
neither                = non-holonomic         (Thue–Morse, (n!)ⁿ, χ, π's CF)
```

Key non-collapses, each witnessed ∅-axiom in the repo:
  - **finite depth ⊊ finite order**: `2ⁿ` is C-finite (`s(n+1)=2s(n)`, order 1) but has *infinite*
    depth (`DepthSelfReference.geom_escapes`).  Depth is the *strictly finer* bottom condition:
    `finite-depth ⊆ finite-order` (`CFiniteHomogRec.order2_homogRec` puts a polynomial's
    constant-coeff recurrence into `HomogRec`) but not conversely.
  - **C-finite ⊊ P-recursive**: `n!` is order-1 P-recursive (`s(n+1)=(n+1)s(n)`, polynomial
    coefficient) but not C-finite.
  - **P-recursive ⊊ all**: `(n!)ⁿ` (`NonHolonomicWitness.superFact_nonHolonomic`), Thue–Morse
    (`ThueMorseRingEscape`, `MorseHedlund`).

## The duality is the founding invert-twin, read at the sequence scale

This is the load-bearing observation.  The number-tower founding (`Lens/Number/`) showed the tower
is built by **one move at two operations** (`PairCompletion.invert_is_one_move`):

  - `ℤ = invert(+)` — the *additive* fold (difference-Lens; sign = period-2 swap),
  - `ℚ = invert(×)` — the *multiplicative* fold (reciprocal involution; determinant `det P`),
  - sharing one unit `1 = NS − NT = det P` (`SharedUnitAcrossReadings.the_unit_is_one_across_readings`).

The two sequence finiteness measures are these *same two folds* iterated:

  | founding (number scale, static) | sequence scale (dynamic) |
  |---|---|
  | `invert(+)` = difference-Lens, ℤ, additive | **depth** = `Δ`-fold (difference calculus) |
  | `invert(×)` = ratio-Lens, ℚ, determinant `det P` | **order** = Casoratian (determinant of shifts) |
  | shared unit `1 = NS−NT = det P` | depth bottoms at the constant/unit; Casoratian floor `det = 1` (Cassini) |

So **depth is the additive-fold reading of finite generation; order is the multiplicative-fold
reading** — and they are the *same invert-twin* the founding identified, now applied to the orbit of
a sequence rather than to a single pair.  The Casoratian's conserved value being the *unit* (`det = 1`
floor, `CassiniDepthFloor.cassini_conserved_depth0`) is literally the founding's shared unit; the
depth bottoming at a constant is the founding's additive unit.  One unit, two folds, two scales.

## The discriminant is the order-2 coupling of the two folds

`tr² − 4·det` mixes the **trace** (additive datum) and the **determinant** (multiplicative datum) —
so the order-2 companion discriminant is *exactly* the quantity that couples the two folds at the
lowest non-trivial order.  This is why it reads off both axes at once
(`EllipticPeriodicTier`, `phi_pi_poles.md`):

  - `Δ = 0` (parabolic) ⟺ the order-2 sequence *also* has finite depth — it is linear
    (`parabolic_iff_depth1`, an iff).  **The discriminant vanishing is precisely "the
    multiplicative-fold-finite sequence is also additive-fold-finite."**
  - `Δ < 0` (elliptic) / `Δ > 0` (hyperbolic): order-2 but *infinite depth* — finite by the
    multiplicative fold (recurrence closes) but never by the additive fold (periodic oscillation /
    exponential growth, not polynomial).

So within a fixed order, the discriminant measures the **residual depth-finiteness** — how much of
the finer (additive) closure survives.  `Δ` is the dial because it is the order-2 *coupling constant*
between the founding's two folds.

**Candidate theorem (clean, tractable, *complements* `parabolic_iff_depth1`):**
> `order2_finite_depth_iff_parabolic` — an order-2 const-coeff sequence has finite difference-depth
> **iff** its discriminant is `0`.  The `⟸` is `parabolic_iff_depth1`; the `⟹` is the new content:
> `Δ ≠ 0` ⟹ infinite depth.  *Elliptic* non-constant ⟹ not eventually monotone ⟹ ¬finite-depth
> (via `PolyDepthMonotone.polyDepthZ_evMono`, since a non-constant periodic sequence oscillates).
> *Hyperbolic* ⟹ exponential growth ⟹ not a polynomial (via `finite_depthZ_iff` + a growth
> separation, or `poly_bound` violated).  Elliptic side is immediately ∅-axiom from existing tools;
> hyperbolic side needs a poly-vs-exp growth lemma.

## The 213 reading, and both ceilings

A sequence is a self-pointing trace.  "Order closes" = the orbit spans finite reachable structure
(`StateMachine.mu_carrier_reachable_reduced_machine`); "depth closes" = the difference-fold reaches
the count-unit.  Both are *the pointing closing into finite reachable structure*, read via the two
founding folds.  The residue = **neither** closes — `spineL_escapes` / `s2Z_not_polyDepthZ` /
`aperiodic_not_autoRec`.  This is the shared ceiling (agent (c) is auditing whether it is literally
one non-surjection theorem); the shared floor is the unit (`FoundingDynamicBridge.
founding_swap_is_elliptic_floor`, done).

So the entire arc is one structure:

> **The founding invert-twin (additive ℤ-fold / multiplicative ℚ-fold, shared unit) is the two
> finiteness measures (depth / order, shared Casoratian-unit) at the sequence scale; the
> discriminant is their order-2 coupling; and the residue is the pointing that closes under
> neither fold — the common top of the number tower and the holonomicity hierarchy.**

## Open threads (agent-assigned)

  1. **order-`k` Casoratian + cubic discriminant** (agent a): general order-`k` Casorati
     conservation; does `Δ₃` (cubic discriminant) give an order-3 trichotomy; where is Tribonacci.
  2. **π reduction + bounded-P-recursive** (agent b): the sharpest conditional `H ⟹ ¬holonomic`
     for π's PQ; is "bounded P-recursive ⟹ eventually periodic" elementary in any special case
     (the time-varying gap).
  3. **unified residue ceiling** (agent c): is the ℝ-Cauchy-unreached non-surjection literally the
     same theorem as the machine-escape — honest verdict, no forced unification.

## Candidate ∅-axiom targets emerging

  - `order2_finite_depth_iff_parabolic` (above) — the depth/order coupling at order 2, made an iff.
  - (pending agent a) an order-3 periodic witness + `cubic_disc` def — the next dial rung.
  - (pending agent c) a unified "reached by no finite stage" schema, *only if* honest.

## Agent findings + corrections (adversarial, integrated)

Two specialist agents returned findings that **correct overclaims** elsewhere in the arc — recorded
here per the "map the boundary, don't force" discipline.

### Ceiling (agent c): the two ceilings are mechanically DISJOINT

Verdict: the residue ceiling is **not one theorem**.  Five distinct proof engines, not one:
Cantor diagonal (`object1_not_surjective`, `cantor_general`), finite-tree leaf-path
(`spineL_escapes`), eventual-monotonicity (`s2Z_not_polyDepthZ`), finite-window pigeonhole
(`aperiodic_not_autoRec`), and *positive convergence* (`CauchyLensFounding.cauchy_lens_founds_on_ratio`
— which states **no escape at all**; it proves the limit *equals* `phiCut`, the opposite polarity).
`object1_not_surjective` is invoked by **neither** the Cauchy side nor the non-holonomicity side
(docstring prose only).  The one genuine shared-engine fact is
`DepthCeilingResidue.ceiling_residue_is_pointing_residue` (residue ↔ ordinal/depth ceiling, both
Cantor) — and it covers neither ℝ nor holonomicity.

**Correction:** the `phi_pi_poles.md` bridge sentence claiming "one non-surjection,
`object1_not_surjective`" for both ceilings is an overclaim and must be softened.  The honest
relationship: *thematically* one ("reached by no finite stage"), *mechanically* disjoint.  An
honest unification is a **shape**, not a proof: a predicate `ReachedByNoStage (e : S → T) (w : T) :=
∀ s, e s ≠ w` that several *escapes* instantiate (each by its own engine), bundled as a conjunction
(à la `DualCollapseCapstone`).  ℝ does **not** qualify until a new escape theorem
`∀ i, phiConvergentSeq.cs i ≠ phiCut` is added (it would join the *shape*, still by a distinct
Fibonacci/irrationality engine).  Note: `object1_not_surjective` (universal: every map misses
something) is strictly stronger than `ReachedByNoStage` (pointwise: this map misses this witness).

### Ceiling, gone DEEPER (the "five engines" verdict was too coarse) — `CeilingSchema`

On re-examination the agent's "five separate engines / separate domains" is a taxonomy of *proof
tactics*, not of *content*.  At the content level **every escape has the same shape**: `∀ stage,
gen stage ≠ target` = `target ∉ range gen` = **`gen` is not surjective**.  Formalized ∅-axiom in
`Lib/Math/CeilingSchema.lean` (5 PURE):
  - `ReachedByNoStage gen target := ∀ s, gen s ≠ target`;
  - `not_surjective_of_reachedByNoStage` — the schema *is* non-surjectivity;
  - instances: `diag_reached` (the universal constructive diagonal — Cantor archetype, `∀ f, ¬
    Surjective f`), `s2Z_poly_reached` (popcount reached by no `newtonZ c d` — the non-holonomicity
    ceiling), and `object1_not_surjective` (the foundational pointing residue) — bundled as
    `ceilings_are_nonsurjectivity`.

So the ceilings are **one phenomenon**: the finite-stage map is not surjective; the target is the
residue surplus, *outside every view's image* (the framework's own reading of the residue, per the
failure-modes catalog).  **Why it looked like separate domains** — the sharp ∅-axiom point:
*classically* one Cantor/cardinality argument settles every ceiling at once (countably many finite
descriptions, "uncountably" many objects); the **∅-axiom discipline forbids that shortcut** (no
`Classical`, no completed uncountable carrier), so each ceiling needs a **named constructive
witness** with a domain-specific escape-proof.  The "five engines" are these *constructive
realizers* of the one non-surjection; the domains are the Lens-carvings.  *One residue, many
constructive witnesses, forced apart by the refusal of the cardinality shortcut.*  Honest residue
kept: universal Cantor (`cantor_general`, ∀ gen ¬surj) ⊋ pointwise `ReachedByNoStage`; and ℝ
(`CauchyLensFounding`, a positive convergence) joins only once `∀ i, convergentᵢ ≠ phiCut` is
supplied.  So the floor (`founding_swap_is_elliptic_floor`) is one theorem AND the ceiling is now
one theorem-schema — both made precise, neither forced.

### Bounded-P-recursive (agent b): it is PROVEN, not open

Major correction: **"bounded + P-recursive ⟹ eventually periodic" is a theorem** (Pólya–Carlson;
Bézivin; Stanley EC2 §6.4), *not* an open problem.  Cleanest proof: bounded + integer D-finite ⟹
generating function has radius 1 and finitely many singularities ⟹ (Pólya–Carlson: integer series
of radius 1 is rational or has the unit circle as natural boundary; D-finite ⟹ finitely many
singularities ⟹ no natural boundary) ⟹ **rational with poles at roots of unity** ⟹ eventually
periodic.  So **Thue–Morse ∉ P-recursive is an established corollary** — and `s2Z_not_polyDepthZ`'s
narrative.

**Correction:** the verdict essay / `G185` framing "dense `HomogRec` escape … shares π's open
status" **conflated non-elementary with open**.  It is *classically settled*; only the **∅-axiom
(elementary)** proof is out of reach — the single hard step is Pólya–Carlson (arithmetic) or
Birkhoff–Trjitzinsky (analytic).  π, by contrast, is *genuinely open*.  Different statuses; fix the
wording.

**The single hard kernel + the formalizable target.**  Elementary special cases exist:
constant/eventually-nonzero leading coefficient (characteristic roots, no structure theorem),
first-order hypergeometric, `{0,1}`-valued via Skolem–Mahler–Lech.  The **time-varying gap** (leading
coefficient vanishing at integers / sign-changing) is reducible to the time-invariant case by
**Poincaré–Perron (1885/1921)** under "`p_d` eventually nonzero with non-degenerate limit roots",
leaving only the *coincident-unit-modulus* kernel genuinely hard.  → recommended formalization
target: the Poincaré–Perron reduction (softer than Birkhoff–Trjitzinsky).

### The π boundary, sharpened (agent b)

The sharpest *statable* conditionals (reduction theorems, open antecedent):
  - **(A, support-only)** `{n : aₙ = 1}` not eventually a finite union of APs ⟹ non-holonomic
    (rigorous via Skolem–Mahler–Lech: holonomic ⟹ zero set is finite ∪ finitely many APs).
  - **(C, single-limit)** the geometric mean `(∏ aᵢ)^{1/n} → ` a transcendental limit (e.g.
    Khinchin's constant) ⟹ non-holonomic (via the structure theorem: holonomic-integer log-means
    are algebraically constrained).
  - **(D, the clarifier)** **no finite-window / forbidden-pattern hypothesis can ever imply
    non-holonomicity** — holonomicity is irreducibly *asymptotic*, not local.  This is *why* every
    elementary witness (`χ`, Thue–Morse, `(n!)ⁿ`) needs an asymptotic certificate (zero-runs,
    aperiodicity, growth), and why π — with **zero** proven asymptotic control of its partial
    quotients (not even unboundedness) — is out of reach.  Theorem D dignifies the whole
    "elementary shadow" framing: the shadows are exactly the asymptotic certificates that happen to
    be ∅-axiom-checkable.
