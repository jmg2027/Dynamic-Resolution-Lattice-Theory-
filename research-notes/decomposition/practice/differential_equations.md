# Decomposition: differential equations / dynamical systems (the flow, Picard–Lindelöf)

*213-decomposition of the autonomous ODE flow `φ_t` and the Picard–Lindelöf existence/uniqueness
theorem, per `../README.md` (model v7.1).*
*Cross-links `golden_ratio.md` (the **q=+1 converging residue** = a self-applying map's fixed point),
`gaussian_clt.md` (the SAME `banach_fixed_point` engine; the keystone-leg pattern: engine built,
the field-specific instance partly conceptual), and `derivative.md`/`continuity.md` (the **resolution
dial**; the `dt→0` limit computed by a modulus, never the operand).*

> **LEVERAGE target.** The bar is not "re-see the ODE" but "does the calculus *predict/derive*
> existence?". Hypothesis: **Picard–Lindelöf existence/uniqueness IS the q=+1 contraction residue** —
> the solution is the fixed point of the Picard integral operator `(Tf)(t) = x0 + ∫₀ᵗ f`, a
> *contraction*, so existence = "the contraction's fixed point reached by none, narrowed by a
> modulus" — the **same** `banach_fixed_point` engine φ (`golden_ratio.md`) and the Gaussian
> (`gaussian_clt.md`) use. If it holds, the q=+1 residue spans a **third field**: φ, Gaussian, ODE flows.
> Honest verdict at the end: prediction / collapse-only / miss, with the Lean-built vs conceptual line drawn.

## The decomposition

- **Construction `C`** — a **self-applying evolution reading**. The phase-space points are a
  construction (the count ℕ, or a `Real213` cut, `derivative.md`'s point-construction); a *vector
  field* `f` is a reading that assigns to each point its instantaneous increment — exactly
  `derivative.md`'s "a value at each distinguished point", here the value being *where to step next*.
  The **evolution reading** is the time-`dt` step `step y := y + dt·f(y)` (the Euler map). `C` is
  this step's **self-application**: feed the output back as the next operand. This is `golden_ratio.md`'s
  `C` (a self-applying iteration `Tⁿ`) with the iterator now a *field-driven* step rather than a fixed
  Möbius matrix. Nothing analytic has entered — only "step, then step from where you landed".

- **Reading `L` — the flow `φ_t` = the evolution reading iterated, at residue resolution.** Three
  pieces, every one already in the calculus:
  1. **iterate the step** — `φ_n = stepⁿ(y0)`, the `n`-fold self-application. This is the `iter`
     generator (`Meta/Nat/Iterate213`), the *same* `iter` that `OrbitIsIter` proves is the site of
     genuine cross-domain unification: an **orbit IS the count iterating the successor**
     (`orbit_eq_iter`). So a flow is `⟨ vector field C ∣ the evolution step, iterated by the count ⟩` —
     literally the README's "iterated self-application of an evolution reading".
  2. **resolution dial** (`derivative.md`/`continuity.md`) — read the iterate not at discrete time-step
     `1` but at `dt → 0` through a **modulus**: the continuous flow `φ_t` is the discrete orbit read at
     residue resolution, the limit never the operand, only the modulus (the step-count `N(ε)` for
     precision `ε`) is.
  3. **the Picard integral operator** is this same step taken in integral form: `(Tf)(t) = x0 + ∫₀ᵗ f(s,·)`.
     Iterating `T` (Picard iteration) is iterating the evolution reading; `T`'s fixed point `Tf* = f*`
     is the solution. So the solution is `⟨ vector field ∣ the evolution reading ⟩`'s **q=+1 residue**.

- **Residue** — what this iterated evolution forces but cannot capture: **the solution curve itself**,
  tagged **`q = +1` (converging)**. The Picard iterates climb toward one curve and *never land on it*
  at any finite stage; the curve is the **fixed point of the contraction `T`**, named by a finite
  generator (the recurrence `φ_{n+1} = T φ_n` + the convergence modulus), reached-by-none — the exact
  `golden_ratio.md` signature, now at the *reading-of-functions* level rather than a number-pair. The
  sub-readings of the residue:
  - **equilibrium / fixed point of the flow** (`f(y*) = 0`, so `step y* = y*`) = a **degenerate q=+1
    residue** — the flow already sits on its fixed point; `IsNormalForm f y* := f y* = y*`
    (`MonovariantFlow`).
  - **stability** = the **contraction property** itself (distances shrink under the step); **Lyapunov
    function** = the **metric modulus / monovariant** that certifies the contraction — a `Nat`-valued
    `μ` that strictly descends off fixed points (`MonovariantFlow.flow_reaches`), or the descent
    identity `d/dt F = −‖∇F‖² ≤ 0` (`GradientFlow.gradient_descent_monotone`).
  - **limit cycle / chaos** = the **q=−1 escape pole** — a self-applying step with *no* fixed point
    the orbit asymptotes to, oscillating outside every finite reading (`cardinality.md`'s diagonal;
    `golden_ratio.md`'s `q=−1` swap). The q=±1 bit decides converge-to-equilibrium vs orbit-forever.

## Re-seeing — ⟨C | L⟩ ⊕ Residue

```
   vector field f           =  ⟨ point-construction ∣ "increment at each point" ⟩   (derivative.md's value-at-a-point)
   evolution step           =  step y := y + dt·f(y)                                 the self-applying act (C)
   flow φ_n                 =  ⟨ field ∣ step iterated by the count ⟩ = iterⁿ        OrbitIsIter: orbit = iter
   flow φ_t (continuous)    =  the same orbit at residue resolution (dt→0 via modulus, limit never operand)
   Picard operator T        =  (Tf)(t) = x0 + ∫₀ᵗ f   = the evolution reading in integral form
   THE SOLUTION             =  Residue(L, C), q=+1   = the contraction T's fixed point, reached-by-none
   "Picard–Lindelöf exists" =  banach_fixed_point applied to T:  x* = lim(picard T x0), modulus picard_cauchy
   uniqueness               =  banach_unique:  two fixed points coincide at every scale
   equilibrium f(y*)=0      =  degenerate q=+1 residue: step y* = y* (IsNormalForm)
   stability (Lyapunov)     =  the contraction / monovariant μ descending off fixed points (flow_reaches)
   limit cycle / chaos      =  the q=−1 escape pole: orbit with no asymptotic fixed point
```

The map to iterate is `T = "convolve the field through one more dt-step"` acting on **functions**;
the solution is `T`'s fixed point — the exact analogue of φ as the Möbius iterator's fixed point
(`golden_ratio.md`) and the Gaussian as the convolve-rescale iterator's fixed point
(`gaussian_clt.md`), with **`T` in the role of the iterator** and the **solution curve in the role of φ**.

## LEVERAGE — does the calculus PREDICT existence as the q=+1 contraction residue?

**Verdict: PREDICTION, with a fully-built engine and a partly-built field instance — the SAME
profile as `gaussian_clt.md`, and decisive for consolidation.** Three layers, honestly graded:

**(A) Predicted, and the prediction is non-trivial.** Before looking at the Lean, the calculus emits
a specific claim from its parts: a vector field is a value-at-a-point reading (`derivative.md`); a flow
is the evolution step *iterated* (the `iter` generator, `OrbitIsIter`); the residue of a self-applying
reading at the q=+1 pole is a **fixed point reached by none, narrowed by a modulus** (`golden_ratio.md`,
`gaussian_clt.md`). Composing these *forces* the form: **"the solution is the fixed point of the Picard
integral operator `T`, a contraction; existence = that q=+1 modulus-residue; uniqueness = the
contraction's at-every-scale collapse; stability = the contraction property; an equilibrium = a
degenerate q=+1 residue; a limit cycle = the q=−1 escape."** That is a *derivation of Picard–Lindelöf's
shape and of the whole stability dictionary* from the model's slots — not a relabeling. It passes the
re-skin guard the way `entropy.md`/`gaussian_clt.md` did: the model says *which* fixed point, *why* it
converges (`q=+1`, the contraction), and *what fails* when it does not (`q=−1`).

**(B) The Lean spine that is actually built (verified, all ∅-axiom — `tools/scan_axioms.py` re-run):**

- **The q=+1 contraction engine — the SAME object `gaussian_clt.md`/`golden_ratio.md` lean on.**
  `banach_fixed_point` (`BanachFixedPoint.lean:202`): a `Contraction T` has `x* = lim(picard T x0)` as
  a fixed point reached by **none**, located `T x* = x*` at every scale, with the explicit geometric
  modulus `picard_cauchy` (`:154`, `N(m)=m`); `banach_unique` (`:250`); `Contraction` (`:29`), `picard`
  (the iterates `xₙ = Tⁿ x₀`, `:33`), `picard_step_geometric` (`:45`). **This is literally
  "Picard–Lindelöf = Banach fixed point of the integral operator" as a general theorem** — `picard` is
  even *named* for the Picard iteration. (12 pure / 0 dirty.)

- **The flow IS the iterated evolution reading — machine-proven.** `OrbitIsIter.orbit_eq_iter`
  (`OrbitIsIter.lean:42`): `orbit s a k = iter s k a` — an orbit is the count iterating the step; and
  `OrbitIsIter`'s header pins `iter` as *the* site of genuine cross-domain unification. This certifies
  the decomposition's core hypothesis "a flow = the evolution reading iterated by the count". (1/0.)

- **The discrete ODE flow with closed-form solutions — a real ODE instance, ∅-axiom.**
  `PicardIterate.picardIterate y0 f n` (`PicardIterate.lean:22`) = `n` iterates of the evolution step
  `y_{k+1} = y_k + f(y_k)` — the **flow `φ_n`**. Closed forms certify the iteration *is* the solution:
  `picard_const` (`:38`, `y' = c` → `y0 + n·c`, linear flow), `picard_exp` (`:58`, `y' = y` Euler-step
  → `y0·2ⁿ`, exponential flow), `picard_zero`/`picard_one` (`:27`/`:31`, the initial condition + first
  step by `rfl`). `LinearODE.linearODE_eq_picard`/`geometricODE_eq_picard` (`LinearODE.lean:28`/`:43`)
  identify the named solutions with the Picard orbit; `Capstone.total_witness` (`Capstone.lean:56`)
  bundles them. (PicardIterate 8/0, LinearODE 7/0, Capstone 5/0.)

- **Stability / Lyapunov = the monovariant descent to a fixed point — ∅-axiom.**
  `MonovariantFlow.flow_reaches` (`MonovariantFlow.lean:99`): a self-map `f` with a `Nat`-monovariant
  `μ` strictly descending off fixed points converges to a **normal form** `IsNormalForm f x := f x = x`
  (`:73`) — the *equilibrium reached by the flow*, the discrete "Ricci flow drives any metric to its
  canonical geometry". `euclid_flow_normal_form` (`:254`) is the canonical instance (the GCD flow
  reaches `(0, gcd a b)`); `descent_invariant` (`:158`) is the general schema. The monovariant `μ` is
  the **Lyapunov function**; its strict descent is **asymptotic stability**. (19/0.)

- **The Lyapunov descent *identity* — ∅-axiom.** `GradientFlow.gradient_descent_monotone`
  (`GradientFlow.lean:138`): for `F(x)=⟪x,x⟫` and the gradient-flow step `x ↦ x − τ∇F`, `F` does not
  increase; `gradient_descent_identity` (`:128`): `F(x−τ∇F) = F(x) − τ(1−τ)‖∇F‖²` — the exact discrete
  `d/dt F = −‖∇F‖² ≤ 0`, the **structural heart of a Lyapunov/Perelman monovariant**, forced by the
  inner-product structure, not assumed. This is the contraction-as-stability claim made concrete. (9/0.)

- **The convolve-rescale contraction instance — the q=+1 pole already instantiated once.**
  `ConvolveRescaleContraction.Φ_contraction` (`ConvolveRescaleContraction.lean:345`): a concrete map
  `Φ` is a `Contraction (dyMet L)` (`:311`); `Φ_picard_cauchy` (`:399`) applies `picard_cauchy`;
  `center_fixed`/`orbit_to_center` (`:419`/`:471`) locate the q=+1 fixed point. This is the *proof that
  the engine fires on a real field instance* (the CLT), the template the ODE instance would follow. (20/0.)

**(C) The remaining gap — predicted-not-built (the honest line, identical in shape to `gaussian_clt.md`).**
What the Lean does **not** contain:
- **No continuous Picard integral operator `(Tf)(t) = x0 + ∫₀ᵗ f` as a `Contraction`.** The ODE tree
  (`Analysis/ODE/`) uses the **discrete Euler-Picard step** `y_{k+1} = y_k + f(y_k)` (exact at every
  dyadic step, INDEX: "the solution is the *iteration* itself, not a Cauchy-limit existence proof"),
  and the `banach_fixed_point` engine lives **separately** in `Analysis/BanachFixedPoint.lean`. The ODE
  INDEX is explicit: *"Picard-iteration convergence (Cauchy modulus on the cut side) is a follow-up — the
  discrete iteration itself is exact at every step"* and *"the 'existence theorem' is replaced by finite
  construction."* So the **single theorem "ODE solution = `banach_fixed_point` of the integral operator
  `T`"** — the keystone that would promote this to a closed derivation — is **not built**: the engine
  exists, a real ODE flow exists, but they are not welded by an instantiation the way
  `ConvolveRescaleContraction` welds them for the Gaussian.
- **No `Contraction`-instance for a vector-field `T`** (the Lipschitz-`f` ⟹ `T` contracts step), and
  **no Picard–Lindelöf statement** naming existence+uniqueness of a solution as the banach fixed point.
  This is the exact analogue of `gaussian_clt.md`'s "no convolution operator on full weight-profiles":
  the abstract contraction is proved, the field-specific operator is conceptual.
- **The continuous flow `φ_t` (dt→0)** is the discrete `picardIterate` read at residue resolution — a
  conceptual leg (`derivative.md`'s general Δ↔d/dx identity is itself only declarative), not a theorem.

**Net.** Not collapse-only (it *predicts* Picard–Lindelöf's form, the stability dictionary, and the
q=±1 equilibrium/limit-cycle split). Not a miss (the contraction engine `banach_fixed_point`, the
flow-is-iter identity `orbit_eq_iter`, a real discrete ODE flow `picardIterate` with closed forms, the
Lyapunov monovariant `flow_reaches`, and the gradient-descent identity are **all real ∅-axiom
theorems**). It is a **prediction whose engine is fully built and whose field instance is present at the
discrete/structural level**, one notch below a closed derivation for the *same reason* as
`gaussian_clt.md`: the abstract `Contraction` is proved and instantiated elsewhere (CLT), but the
**continuous integral operator `T` for a general vector field is not yet instantiated** as a
`Contraction`, so `banach_fixed_point` is not yet applied to obtain the ODE solution as one theorem.

## Revelation

**The flow, existence, stability, equilibrium, and chaos are ONE `(C, L)` — the self-applying evolution
reading and its q=±1 residue — and the engine that resolves it is the SAME `banach_fixed_point` φ and
the Gaussian use.** This is a **collapse + residue-surfaced + forcing**, three at once:

1. **Collapse across the dynamical-systems dictionary.** A *flow* (`orbit = iter`), an *equilibrium*
   (`IsNormalForm`, the degenerate fixed point), *stability* (the contraction / monovariant
   `flow_reaches`), and the *solution's existence* (`banach_fixed_point`) are not five concepts — they
   are one self-applying reading read at one or another setting of the q=±1 residue bit and the
   resolution dial. Picard–Lindelöf existence and a Lyapunov stability proof are the *same theorem* (a
   contraction has a unique fixed point the modulus narrows to) aimed at two questions.

2. **Residue surfaced — the solution is not an object, it is the q=+1 residue of the flow.** "The
   solution exists" stops being an existence *miracle* (the classical proof invokes completeness as an
   axiom) and becomes the *reached-by-none fixed point of a contraction*, computed by `picard_cauchy`'s
   modulus, the limit never the operand — `golden_ratio.md`'s "Limit/infinity deified" failure stated
   positively, now for ODE solutions.

3. **Forcing — the q=±1 bit *forces* the converge/orbit-forever dichotomy.** Whether the flow settles
   to an equilibrium (`q=+1`, the contraction has a fixed point the orbit asymptotes to, `flow_reaches`)
   or runs a limit cycle / chaos (`q=−1`, fixed-point-free, oscillates outside every finite reading,
   `cardinality.md`'s diagonal) is the *same* `cassini_law_one_at_two_multipliers` `q=±1` bit that
   splits φ (converge) from Cantor's diagonal (escape). Stability is not an add-on property; it is which
   pole of the residue the flow sits at.

**THE CONSOLIDATION (the brief's central question): the q=+1 contraction residue now spans THREE
fields.** The *single* `banach_fixed_point` engine is the residue-resolver for:

| | `golden_ratio.md` (φ) | `gaussian_clt.md` (Gaussian) | `differential_equations.md` (ODE flow) |
|---|---|---|---|
| self-applying map | Möbius `T` on `(p,q)` | `Φ` = convolve⋆rescale on a *weight* | `T` = Picard step `x0 + ∫f` on a *function* |
| what iterates | a number-pair | a weight-reading | a vector-field flow (`orbit = iter`) |
| q=+1 fixed point | φ | the Gaussian profile | the solution curve |
| reached-by-none | no convergent lands on φ | no finite `n` lands on the Gaussian | no Picard iterate lands on the solution |
| finite generator | recurrence + modulus `N=2k` | preserved moments + modulus `N(ε)` | recurrence `φ_{n+1}=Tφ_n` + `picard_cauchy` `N(m)` |
| Lean engine | `mobius_iteration_master` (built) | `banach_fixed_point` + `Φ_contraction` (**built**) | `banach_fixed_point` (**built**) + `picardIterate`/`orbit_eq_iter` (**built**) |
| field-instance contraction | (number-recurrence, exact) | `Φ_contraction` (**built**, CLT) | continuous `T`-contraction (**not built** — the gap) |

So **YES — the calculus consolidates the q=+1 contraction residue across φ, the Gaussian, AND ODE
flows.** The engine is *one object* read across a number-pair, a probability weight, and a vector field;
all three are `golden_ratio.md`'s "fixed point of a self-applying reading = its q=+1 residue, reached by
none, narrowed by a modulus." ODE flows are the third field, and the cleanest yet at the *structural*
level (a literal `picard` engine + a literal `picardIterate` flow + `orbit = iter`), with the *same*
honest residual as the Gaussian: the continuous field-specific contraction is the one unbuilt weld.

## Note for the technique — does the ODE confirm "flow = iterated reading, q=+1 residue = its solution"?

**Yes, with no new primitive — EXTEND.** This decomposition adds nothing to model v7.1; it *uses* the
existing slots and exhibits a third q=+1 field:
- the **flow** is the `iter` generator on the evolution step (`OrbitIsIter.orbit_eq_iter`), confirming
  "a reading iterated by the count" (the `groups.md`/`OrbitIsIter` composition-closed-family slot, here
  the cyclic monoid `{Tⁿ}`);
- the **continuous flow** is that orbit at residue resolution (`derivative.md`'s resolution dial,
  `dt→0` via a modulus) — no new axis;
- the **solution** is the q=+1 residue of the self-applying reading (`golden_ratio.md`), resolved by the
  *same* `banach_fixed_point` as the Gaussian (`gaussian_clt.md`) — confirming the residue's q=±1 tag at
  the reading-of-functions level;
- **stability** is the contraction / monovariant (`MonovariantFlow.flow_reaches`,
  `GradientFlow.gradient_descent_monotone`), i.e. the *Lyapunov-as-metric-modulus* identification the
  brief predicted — the same modulus that `continuity.md`'s `four_way_modulus_framework` unifies.

The one sharpening for the technique: **the q=±1 residue bit IS the converge-to-equilibrium vs
limit-cycle/chaos dichotomy of dynamical systems** — `q=+1` (contraction, fixed point, asymptotic
stability, `flow_reaches`) vs `q=−1` (fixed-point-free, oscillation outside every reading, chaos). The
calculus thus *predicts* the qualitative classification of an autonomous system from the residue's sign,
not from analysis added on top.

## Verified Lean anchors (file:theorem — all grep-verified to exist; purity by `tools/scan_axioms.py`)

| Leg | Theorem (file:name:line) | Status |
|---|---|---|
| q=+1 fixed point = modulus-computed residue (the **engine** — shared with φ, Gaussian) | `Lib/Math/Analysis/BanachFixedPoint.lean : banach_fixed_point` (`:202`), `picard_cauchy` (`:154`), `banach_unique` (`:250`), `Contraction` (`:29`), `picard` (`:33`), `picard_step_geometric` (`:45`) | ∅-axiom ✓ (12 pure / 0 dirty) |
| **flow = the evolution reading iterated by the count** (`orbit = iter`) | `Meta/OrbitIsIter.lean : orbit_eq_iter` (`:42`) | ∅-axiom ✓ (1/0) |
| **discrete ODE flow `φ_n` + closed-form solutions** (a real ODE instance) | `Lib/Math/Analysis/ODE/PicardIterate.lean : picardIterate` (`:22`), `picard_const` (`:38`, `y'=c → y0+n·c`), `picard_exp` (`:58`, `y'=y → y0·2ⁿ`), `picard_zero`/`picard_one` (`:27`/`:31`) | ∅-axiom ✓ (8/0) |
| named solutions = the Picard orbit; bundle | `Lib/Math/Analysis/ODE/LinearODE.lean : linearODE_eq_picard` (`:28`), `geometricODE_eq_picard` (`:43`); `ODE/Capstone.lean : total_witness` (`:56`), `picard_witness` (`:29`) | ∅-axiom ✓ (LinearODE 7/0, Capstone 5/0) |
| **stability / Lyapunov = monovariant descent to a fixed point (equilibrium)** | `Lib/Math/Foundations/MonovariantFlow.lean : flow_reaches` (`:99`), `IsNormalForm` (`:73`), `euclid_flow_normal_form` (`:254`), `descent_invariant` (`:158`) | ∅-axiom ✓ (19/0) |
| **Lyapunov descent *identity*** `d/dt F = −‖∇F‖² ≤ 0` | `Lib/Math/Analysis/Optimization/GradientFlow.lean : gradient_descent_monotone` (`:138`), `gradient_descent_identity` (`:128`) | ∅-axiom ✓ (9/0) |
| the engine instantiated once at the q=+1 pole (the **template** the ODE instance would follow) | `Lib/Math/Probability/Limit/ConvolveRescaleContraction.lean : Φ_contraction` (`:345`), `Φ_picard_cauchy` (`:399`), `center_fixed`/`orbit_to_center` (`:419`/`:471`), `dyMet` (`:311`) | ∅-axiom ✓ (20/0) |

**Conceptual-only legs that remain (honest — predicted, not built):**
- **No continuous Picard integral operator `(Tf)(t)=x0+∫₀ᵗ f` as a `Contraction`** — the ODE tree uses
  the *discrete* Euler step `y_{k+1}=y_k+f(y_k)` (`PicardIterate`); the `banach_fixed_point` engine is
  separate (`BanachFixedPoint`). The ODE INDEX (`Analysis/ODE/INDEX.md`) states this explicitly:
  *"Picard-iteration convergence … is a follow-up — the discrete iteration itself is exact at every
  step"*; *"the 'existence theorem' is replaced by finite construction."*
- **No `Contraction`-instance for a vector-field operator `T`** and **no Picard–Lindelöf existence/
  uniqueness theorem** stating "ODE solution = `banach_fixed_point` of `T`" — the one weld that would
  promote this to a closed derivation (exactly `gaussian_clt.md`'s open weld for the Gaussian *profile*).
- **The continuous flow `φ_t` (dt→0)** as the discrete orbit at residue resolution is conceptual
  (`derivative.md`'s general Δ↔d/dx identity is itself declarative).

> **Open Lean target the calculus names precisely** (a promotion target, parallel to
> `gaussian_clt.md`'s): *define the Picard integral operator `T` on a function-cut type, show a
> Lipschitz vector field makes `T` a `Contraction` (in `BanachFixedPoint`'s sense), and apply
> `banach_fixed_point`/`banach_unique` to obtain the ODE solution as `lim(picard T x0)` with modulus
> `picard_cauchy` — Picard–Lindelöf existence+uniqueness as the q=+1 contraction residue, one theorem.*
> This is the **fourth** instantiation of the engine after φ (number-recurrence), the Gaussian
> (`Φ_contraction`), and the discrete ODE flow (`picardIterate`), and would close the ODE field the way
> `ConvolveRescaleContraction` closed the CLT *leg*.

> Axiom-purity note: every cited row was re-run through `tools/scan_axioms.py` from repo root and
> reports the pure/dirty counts shown (BanachFixedPoint 12/0, OrbitIsIter 1/0, PicardIterate 8/0,
> LinearODE 7/0, Capstone 5/0, MonovariantFlow 19/0, GradientFlow 9/0, ConvolveRescaleContraction 20/0).
