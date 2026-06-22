# Decomposition: the derivative / rate of change (and its discrete shadow Δ)

*213-decomposition of `d/dx` and the finite difference `Δ`, per `../README.md`.*
*Cross-links `practice/integers.md` — the derivative is the SAME difference-reading
that builds ℤ, applied to a function's adjacent values.*

## The decomposition

- **Construction `C`** — a **function as a reading-over-a-construction**. The points
  are themselves a construction (the count ℕ, or a `Real213` cut); a function `f` is a
  reading that assigns a value (itself a construction) to each point. So `C` here is
  *two-layered*: a construction of points, with a value-construction hung at each.
  Nothing analytic has entered yet — `f` is just "a value at each distinguished point".
- **Reading `L_Δ`** — the **difference-reading on adjacent values**:
  `Δf(x) = f(x+1) − f(x)`. This is **not a new reading**. It is `L₋ = (m,n) ↦ m − n`
  from `integers.md` — the difference-Lens — applied to the *adjacent value pair*
  `(f(x+1), f(x))`. In Lean this identity is literal: the forward difference is
  `diffZ s n := s (n+1) − s n` (`NewtonGregory.lean:54`), and that `−` is `Int`'s
  subtraction, i.e. the readout of `npairToInt`/`Int.subNatNat` that `integers.md`
  decomposes. **Δ = `L₋` aimed at adjacent values; no second primitive.**
- **The derivative `f'`** = the *same* reading `L_Δ` taken **in the residue** — the
  difference quotient `(f(x+h) − f(x))/h` read through a **modulus** as `h` shrinks. The
  numerator is still `L₋`; "the limit" is never the operand. 213 computes with the
  **modulus** `N(m,k)` (the finite generator that says how fine `h` must be for
  precision `k`), the limit itself being the residue's *shape*, not a held object.
- **Residue** — what `L_Δ` forces but cannot capture. Two faces, and they are one:
  1. *Discrete face*: like `L₋` on ℤ, `Δ` is many-to-one — it forgets the constant
     (any `f` and `f + c` have the same `Δf`). The forgotten constant is the
     anti-difference's residue (the "+C" of integration), recovered only by
     **telescoping** (`Σ Δ = f(b) − f(a)`).
  2. *Continuous face*: the limit `f'` is **the residue of the difference-quotient
     reading** — reached by no finite `h`, only narrowed by the modulus. This is the
     CLAUDE.md "Limit/infinity deified" failure stated positively: the limit is the
     reading's surplus, computed via its finite signature (the modulus), never grasped.

## Re-seeing

```
   Δf           =  ⟨ value-pair (f(x+1), f(x)) | L₋ = (m − n) ⟩          -- discrete resolution
   f'(x)        =  ⟨ value-pair (f(x+h), f(x))  | L₋ ⟩ / h,  read in the residue
                   (operand = the MODULUS N(m,k), never "the limit")     -- residue resolution
   "+C" / sign  =  the constant L_Δ forgets  =  L₋'s anti-diagonal, exactly as in ℤ
   ∫ (the FTC)  =  telescoping Σ Δ = f(b) − f(a):  un-forgetting the residue
```

So `Δ` and `d/dx` are **one reading at two resolutions** of the point-construction:
counts adjacent at step `1` (discrete) versus adjacent in the residue (`h → 0` via a
modulus). The "rate of change" is not analytic content added on top of subtraction; it
is subtraction (`L₋`) read at a chosen resolution.

## Revelation (collapse + residue-surfaced)

The derivative is **not a new analytic primitive**. It is the **difference-reading `L₋`
that already builds ℤ** (`integers.md`), aimed at a function's adjacent values
(`Δf(x) = f(x+1) − f(x)`, Lean-literal as `diffZ s n = s(n+1) − s n`), and at the
*continuous* resolution read through a **modulus** rather than "a limit". This is a
**collapse**: discrete `Δ` and continuous `d/dx` are *one* `(C, L₋)` evaluated at two
resolutions — same arrow, the only difference being how "adjacent" is decided
(step-1 vs. modulus-fine). And it is a **residue surfaced**: the integration constant
"+C" is exactly `L₋`'s anti-diagonal forgetting (the same residue that makes ℤ's
`(m,n)↦m−n` many-to-one), and "the limit" `f'` is the *residue of the
difference-quotient reading*, computed by its finite signature (the modulus), the limit
itself never being the operand.

## Lean grounding — which legs are certified, which are conceptual (honest)

**Certified (verified to exist, docstrings assert ∅-axiom):**

- *Δ IS the difference-Lens.* `Cauchy/NewtonGregory.lean:54` —
  `def diffZ (s : Nat → Int) : Nat → Int := fun n => s (n + 1) - s n`. The forward
  difference is literally `f(n+1) − f(n)` over `Int`, i.e. `L₋` (`Int.subNatNat`,
  `npairToInt`) of `integers.md`. **This is the cross-link, exact and machine-level.**
- *Resolution = depth (the "two resolutions" made into a theorem).*
  `NewtonGregory.lean:59` `liftKZ` (k-fold forward difference),
  `:188` `polyDepthZ d s := isConstZ (liftKZ d s)`, and
  `Cauchy/DepthCharacterization.lean:59` `polyDepthZ_succ_of_diff`
  ("a difference drops the depth by one") — applying `Δ` lowers resolution-depth by 1.
- *Δ as a structural operator (Pascal's rule).* `DepthCharacterization.lean:72`
  `diffZ_binomColZ : diffZ (binomColZ (k+1)) n = binomColZ k n` — `Δ` of a binomial
  column is the next column down. Newton-forward-difference machinery is real and ℤ-built.
- *Telescoping = discrete FTC / antidifference (the residue un-forgotten).*
  `Cauchy/CasoratianStep.lean:101` `telescope` (`∏P·g(n) = ∏Q·g(0)`) and
  `:115` `telescope_geometric`. Multiplicative form here; the additive
  `Σ Δ = f(b)−f(a)` shape also appears as `FluxMVT/FluxFTC.lean` (`ftc_id_unitBracket`,
  `ftc_const`), though those are specific witnesses, not the general law.

**Conceptual-only (honest — Lean is thin or declarative here):**

- *The continuous derivative as the residue-resolution reading.*
  `Differentiation/DifferenceQuotient.lean` is **interface/declarative only**: it
  defines `DifferentiableAt` carrying a `modulus : Nat → Nat → Nat` and gives the
  *constant* function's derivative (modulus ≡ 0). The "difference quotient converges via
  the modulus" claim is stated, **not proved in general** there.
- *Concrete polynomial derivatives via modulus.*
  `Differentiation/PolySumDerivativeModulus.lean:46,52,63,86`
  (`affineIsDifferentiable_derivative_modulus`, `…square…`, `…cube…`,
  `polynomial_sum_derivative_capstone`) are **verified to exist** and give derivative
  *moduli* for affine/quadratic/cubic polynomials — real, but **specific cases**, not
  the general "`f'` = `L_Δ` in the residue" theorem. They certify that 213 carries the
  derivative as a modulus, not that Δ-and-d/dx collapse in general.
- *Resolution as a graded axis.* `ResolutionShift.lean` proves `IsResolutionShift`
  forms a graded `(ℕ,+)` monoid free on one generator (`cutHalf`) — suggestive support
  for "resolution is a parameter" but **about cut-transformers, not about Δ/d directly**;
  the link to the derivative's resolution is conceptual.

So the **discrete leg is fully Lean-certified** (Δ = `L₋`, depth-drop, telescoping); the
**continuous leg is real-but-partial** (modulus-carrying derivative exists for concrete
polynomials; the general convergence is declarative). The *collapse claim* — "Δ and d/dx
are one reading at two resolutions" — is **certified on the discrete/depth side and
conceptual on the bridge to the limit**. Stated honestly: 213 has the difference-Lens
and resolution-depth as theorems, and the derivative-as-modulus as concrete instances;
the fully general Δ↔d/dx identity is not yet a single Lean theorem.

> Axiom-purity note: the cited files' docstrings assert "∅-axiom" / "All zero-axiom"
> (`NewtonGregory`, `CasoratianStep`, `NatPairToInt`). I could not re-run
> `tools/scan_axioms.py` in this environment (the probe-path write failed, a tooling
> cwd bug, not a theorem failure), so the purity claim here rests on the in-file
> docstrings, not a fresh scan.

## Note for the technique — the **resolution parameter** on a Reading

This decomposition forces a concrete answer to a shape-question the README did not yet
ask: **a Reading should carry a `resolution` parameter** — the same Lens `L` evaluated
at "adjacency" defined by a step (discrete) or by a **modulus** (residue). Under that
parameter, several classically-separate pairs collapse to *one reading at two settings*:

| Reading `L` | discrete resolution | residue resolution |
|---|---|---|
| difference `L₋` | `Δf = f(x+1) − f(x)` | `f' = L₋/h` via modulus |
| anti-difference | telescoping `Σ Δ` | integral `∫` |
| (count, summation) | `Σ` | `∫` (measure) |

The README's open shape-question **"should fold-height / resolution be an explicit
readable feature?"** gets a *yes* with a specific mechanism: **resolution is not a new
axis of `C` but a parameter on `L`** — how finely "adjacent" is decided. `Δ`/`d`,
`Σ`/`∫`, and the depth-tower (`liftKZ`, `polyDepthZ`) are then the *same* readings dialed
across resolution, with "the limit" never an operand — only the modulus is. This also
sharpens the `integers.md` note: there the open question was whether **direction** is a
first-class axis of `C` (yes — ℤ's sign). Here the answer is the complementary one:
**resolution** is a first-class parameter of `L`. `C` carries direction; `L` carries
resolution; the difference-Lens `L₋` is where both meet (ℤ = direction-axis of `C` under
`L₋`; `d/dx` = residue-resolution of `L₋`).
