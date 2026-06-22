# Decomposition: integration / measure (∫, the integral)

*213-decomposition of the integral `∫` and the Fundamental Theorem of Calculus, per `../README.md`
(model v6). Directly cashes a prediction made in `practice/derivative.md`: that `Σ`/`∫` is the
**same sum-reading at two resolutions** exactly as `Δ`/`d` is one difference-reading at two
resolutions — and that the **FTC is telescoping read at residue resolution** (∫ inverts d the way
Σ inverts Δ). This note tests whether that prediction FALLS OUT or is collapse-only.*

## The decomposition (C / Reading / Residue)

- **Construction `C`** — the same two-layered point-construction as `derivative.md`: a construction
  of points (a `Real213` cut / dyadic bracket-tree, points = refinement residues, never held) with a
  value-construction hung at each. A function `f` is a reading-over-`C`; `∫` reads `f` back over a
  *chain* of adjacent brackets. Nothing measure-theoretic enters — there is **no `Ω`, no σ-algebra,
  no `Measure` type**; the construction is the dyadic bracket-chain and the readout is a `(num,den)`
  cut. (Lean: `Integration/CutRiemann.lean`, `DyadicBracket`.)

- **Reading `L_Σ` — the sum-reading (accumulation), the additive twin of `L₋`.** Where `derivative.md`
  aimed the difference-Lens `L₋ = (m,n)↦m−n` at *adjacent values*, the integral aims its **inverse,
  the accumulation/anti-difference**, at a *chain* of brackets. Concretely:
  - **discrete resolution** — `Σ` over steps: the running-product/running-sum that carries a one-step
    law back to the start, i.e. **telescoping** (`CasoratianStep.telescope`). This is the discrete
    antidifference: `Σ Δf = f(b) − f(a)`.
  - **residue resolution** — `∫`: the *same* accumulation read through a **modulus** as the step
    shrinks. The operand is never "the limit"; it is the finite **Cauchy modulus `N(m,k)`** that says
    how fine the partition must be for precision `k` (`RiemannIntegralData.modulus`,
    `CutRiemann.lean:79`). `∫` = `Σ` dialed from step-1 to residue, exactly mirroring `f' = Δf`
    dialed to `h→0`.

- **Residue** — what `L_Σ` forces but cannot capture, in two faces that are one (the mirror of
  `derivative.md`'s):
  1. *Discrete face*: accumulation forgets where it started — the antidifference is defined only up to
     the constant `Δ` had forgotten (the "+C"). Telescoping is precisely the act that **un-forgets**
     it by fixing the boundary `f(a)`.
  2. *Continuous face*: the integral's value is the residue of the Riemann-sample reading — reached by
     no finite partition, only narrowed by the modulus `N(m,k)`. This is `derivative.md`/`continuity.md`'s
     **same modulus residue**, not a new transcendent (the "Limit/infinity deified" failure stated
     positively: the modulus is the operand, the limit never is).

## Re-seeing — ⟨C | L⟩, ∫ = Σ at residue resolution

```
   Σ Δf            =  ⟨ bracket-chain | L_Σ = accumulate ⟩                  -- discrete resolution
                      telescoping: (∏P)·g(n) = (∏Q)·g(0)  /  Σ Δf = f(b)−f(a)
   ∫_a^b f dx      =  ⟨ Riemann samples of f over the chain | L_Σ ⟩,
                      read in the residue (operand = MODULUS N(m,k), never "the limit")
   the "+C"        =  the start-point L_Σ must be GIVEN  =  L₋'s anti-diagonal (derivative.md)
   FTC             =  telescoping at residue resolution:  ∫ f' = F(b) − F(a)
                      = fluxAlong F over the bracket (interior sum collapses to the boundary)
```

So `Σ` and `∫` are **one reading at two resolutions** of the bracket-chain — accumulation with
"adjacent" decided by step-1 (telescoping `Σ`) versus by a modulus (`∫`). The integral is not new
analytic content stacked on summation; it is **summation read at residue resolution**, the exact
additive mirror of `f' = Δ at residue resolution`. The calculus's prediction from `derivative.md`'s
table (`anti-difference: telescoping Σ | integral ∫`) is realized: the bottom-right cell *is* the
top-left cell at a dialed resolution.

## LEVERAGE — does the FTC fall out of telescoping at residue resolution?

**Verdict: PREDICTION (not collapse-only), at the structural/skeleton level — and it is unusually
well-Lean-backed for this batch.** The calculus predicts the FTC's *form and why* before importing any
measure theory, and the prediction is cashed at three escalating Lean levels:

**(1) The integral is DEFINED as the inverse of `d` — `∫` inverts `d` the way `Σ` inverts `Δ` is
literal, not analogical.** `IsAntiderivative F sF f` is *exactly* `sF.derivative = f`
(`Integration/Antiderivative.lean:54`). The definite integral is then `integral hF db := fluxAlong F db`
(`IntegralViaAnti.lean:42`), and **`integral_eq_flux` (`:47`, `rfl`)** says the integral *is* the flux
of the antiderivative along the bracket — i.e. `∫_a^b f dx = F(b) − F(a)` holds **by definition-unfolding**
once `F` is the antiderivative. The "+C" residue surfaces exactly as predicted: `IsAntiderivative`
fixes `F`'s derivative but not `F`'s value, so the boundary `F(a)` must be *given* — the start-point
`L_Σ` forgot, the anti-diagonal of `derivative.md`.

**(2) The FTC = telescoping is a single ∅-axiom theorem — the prediction's keystone.**
`TelescopingConservation.gauss_conservation_telescope` (`:152`, "All declarations PURE") proves that
along a bracket-chain every **interior wall cancels** (`(fluxAlong f db_i).forward = (fluxAlong f
db_{i+1}).backward`) and only the **outer boundary cuts survive** (`= f db₀.leftCut`, `f db₂.rightCut`).
That is telescoping made literal: the interior sum collapses to the boundary value — the additive FTC
`Σ Δ = f(b)−f(a)` and the divergence theorem `∫_Ω ∇·F = ∮_∂Ω F` as **one** edge-matching identity, "no
integral / measure machinery needed; the cancellation IS the conservation." This is the discrete FTC
(`CasoratianStep.telescope`, `:101`, `(∏P)·g(n) = (∏Q)·g(0)`) carried to the bracket-chain. The
calculus *predicted* FTC as the residue-resolution image of the telescoping Σ/Δ inverse; the repo has
it as a proved theorem.

**(3) `Σ`-at-residue is genuinely the modulus residue, and meets the boundary value at depth 0.**
`RiemannIntegralData` (`CutRiemann.lean:75`) carries the Riemann approximation `approx` together with a
Cauchy **modulus** `N(m,k)`, and `RiemannIntegralData.limit := approx (modulus m k) m k` (`:86`) — the
integral's value is *read at the modulus index*, the limit never an operand (the residue computed by
its finite signature, exactly `continuity.md`/`derivative.md`). And `FTCRiemann.ftc_riemann_id_depth_zero`
(`FTCRiemann.lean:79`) closes the loop: the Riemann sum of `id`'s derivative over the unit bracket
**equals the boundary flux** `(fluxAlong id unitBracket).forward` — Σ-side and boundary-side agree.
`ftc_riemann_square_depth_zero_at` (`:117`) gives the same for `x²` pointwise. So the two readings
(accumulate-the-interior vs. read-the-boundary) are proved equal — the FTC — at concrete depth.

**Honest boundary — Lean-built vs. conceptual.** The prediction is genuine, not re-skin (it derives
FTC's form + why from the Σ/Δ inverse, with `gauss_conservation_telescope` as the proved keystone),
but the **general convergent ∫ over arbitrary `f`** is *not* one theorem:
- *Lean-built (∅-axiom, verified):* (a) integral = inverse-of-d by definition (`IsAntiderivative`,
  `integral_eq_flux`); (b) FTC = telescoping = boundary-collapse (`gauss_conservation_telescope`,
  `flux_quad_telescope`, `CasoratianStep.telescope`); (c) integral linearity (`integral_add`,
  `integral_mid`, `IntegralProperties.lean:58,67`); (d) Σ-at-residue via modulus + Σ=boundary at
  depth 0 for `id`, `x²` (`RiemannIntegralData.limit`, `ftc_riemann_id_depth_zero`,
  `ftc_riemann_square_depth_zero_at`); (e) constant integral converges with modulus 0
  (`unitConstRiemann_limit`).
- *Conceptual-only (honest):* the **general** "`∫ f'` over an arbitrary bracket equals `f(b)−f(a)` for
  every differentiable `f`" is assembled from *witness cases* (`id`, constant, `x²`, mid) and the
  telescoping skeleton — there is **no single `forall f, ftc` theorem** for arbitrary `f`. The
  depth-0 Riemann=boundary equalities are *specific witnesses*; the general "Riemann limit = boundary
  for all `f`" is the named-open analytic completion (the same edge as `derivative.md`'s general
  Δ↔d/dx and `probability.md`'s general weighted-measure-at-limit). And `∫_a^b c = c·(b−a)` for
  general `(a,b)` is flagged in-repo as "a separate arc" needing signed cut subtraction
  (`CutRiemann.lean:108`); only `(0,1)` is closed.

So: **prediction, cashed on the discrete/telescoping spine and on concrete witnesses; the
all-`f` analytic convergence is the named open target, not a hand-wave.**

## Note for the technique — does ∫ confirm resolution UNIFIES Δ/d AND Σ/∫ as one dial?

**Yes, decisively — and this is the strongest single confirmation of the resolution parameter to date,
because it closes the prediction `derivative.md` *wrote down but did not yet cash*.** The four cells of
`derivative.md`'s table are now all anchored:

| Reading | discrete resolution | residue resolution | Lean anchor (both ends) |
|---|---|---|---|
| difference `L₋` | `Δf = f(x+1)−f(x)` | `f' = L₋/h` via modulus | `NewtonGregory.diffZ`; `PolySumDerivativeModulus` |
| **accumulation `L_Σ`** (inverse) | **telescoping `Σ Δ = f(b)−f(a)`** | **`∫` via modulus** | `CasoratianStep.telescope`; `RiemannIntegralData.limit` |

Three technique-level findings:

1. **The resolution dial is *reading-agnostic*: it dials `L₋` (→ Δ/d) AND its inverse `L_Σ` (→ Σ/∫)
   with the same mechanism (step-1 vs. modulus `N(m,k)`).** Resolution is confirmed as a parameter on
   the *reading slot itself*, not tied to one Lens — it commutes with taking the inverse reading. This
   matches `continuity.md`'s lesson (resolution is the organizing axis of a discipline) and extends it:
   the dial respects the difference↔accumulation inverse-pair.

2. **The FTC = "telescoping is resolution-invariant."** The single deepest shape-note: `Σ` inverts `Δ`
   (discrete telescoping) and `∫` inverts `d` (FTC) are **the same inverse-relation read at two
   resolutions**. The FTC is not a new theorem bridging two realms; it is the statement that *the
   Σ/Δ adjoint survives the resolution dial* — the interior-cancels-to-boundary identity holds at
   step-1 (`telescope`) and at residue (`gauss_conservation_telescope`, `integral_eq_flux`) with the
   *same* boundary-collapse shape. "FTC = telescoping is resolution-invariant" is the precise,
   Lean-anchored form.

3. **Completes the `derivative.md`/`continuity.md` resolution story — the residue-side `q=±1` slots
   in.** `derivative.md` opened the dial on a single reading; `continuity.md` made it a discipline
   (commute / fibre / residue); this note closes the loop by cashing the *inverse* cell and showing
   the dial carries the **adjoint structure** (Δ ⊣ Σ, the discrete shadow of `d ⊣ ∫`). The integral's
   residue is the **converging `q=+1`** pole (the modulus *asymptotes to* a value — `unitConstRiemann`'s
   modulus is literally `0`, instant convergence; general modulus narrows toward the cut), the additive
   mirror of `derivative.md`'s difference-quotient residue. No new primitive: ∫ EXTENDS the model as
   `L_Σ` (= `L₋`'s inverse reading) dialed to residue resolution, with FTC = the dial's invariance of
   the Δ⊣Σ adjoint.

> Axiom-purity note: cited files assert PURE / ∅-axiom in docstrings (`TelescopingConservation.lean:46`
> "All declarations PURE", `:133` "∅-axiom statement"; `Integration/INDEX.md`). I did not re-run
> `tools/scan_axioms.py` in this environment; the purity claim rests on in-file docstrings + INDEX,
> not a fresh scan.
