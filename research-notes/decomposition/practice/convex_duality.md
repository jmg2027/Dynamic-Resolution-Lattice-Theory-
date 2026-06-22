# Decomposition: convex optimization / duality (convexity, Legendre–Fenchel, Lagrangian duality, KKT)

*213-decomposition of convex duality, per `../README.md` (model v7.1). The bar is **leverage /
revelation, consolidating four prior entries**: `galois.md` (the order-reversing adjoint pair →
closure), `adjunction.md` (the adjoint pair → idempotent closure monad `clo`), `differential_equations.md`
(gradient flow = the `q=+1` descent to a fixed point), and `spectral.md`/`Mat2SymmetricSpectrum`
(the symmetric `disc≥0` = the real-nonneg / `q=+1` corner). Hypothesis: convex duality is not a new
field — it is **`galois.md`'s order-reversing adjunction read on functions**, with the four classical
pillars falling out as the four invariants already built.*

This entry is split into a **grounded core** (the abstract adjunction/closure, the gradient-descent
`q=+1` fixed point, the symmetric-PSD corner, and — the surprise — a real ∅-axiom **weak-duality /
minimax** theorem) and a **flagged conceptual leg** (the Legendre–Fenchel *transform object* `f*`, the
biconjugate `f**`, and the named KKT/subgradient apparatus — all **absent**, located precisely like
`knots.md` located its missing primitive).

## The decomposition (C / Reading / Residue)

- **Construction `C`** — a construction with a **fold-height / curvature** sub-structure
  (`README` model v4: `C` carries a bidirectional fold-height) read as *second-order increment*. The
  objects are functions on a point-construction (`derivative.md`'s value-at-a-point); **convexity** is
  the condition that the second difference is `≥0` — the height-reading run twice, nonneg. On the
  matrix shadow this is exactly the Hessian being PSD = the **symmetric operator's discriminant `≥0`**
  (`Mat2SymmetricSpectrum.disc_symmetric_nonneg`), the `q=+1` real-nonneg-spectrum corner of
  `spectral.md`.

- **Reading `L`** — **the same order-reversing adjoint pair as `galois.md`, read on functions.** The
  Legendre–Fenchel transform `f*(p) = sup_x (⟨p,x⟩ − f(x))` is an order-reversing map on the lattice
  of functions (point-wise `≤`), and its companion is itself: `f ↦ f*` is its own adjoint up to the
  pairing, so `Fix = Inv = (·)*` and the closure is `clo(f) = f** = (·)*∘(·)*`. This is *literally*
  `galois.md`'s `clo = Inv∘Fix` (`adjunction.md`'s idempotent closure monad `T = G∘F`), with the two
  reading-families being functions-on-`x` and functions-on-`p` (primal/dual variable), and the order
  reversed by the `sup`. The **Lagrangian** `L(x,λ) = f(x) + ⟨λ, g(x)⟩` is the same pairing
  internalised; the **dual function** `q(λ) = inf_x L(x,λ)` is the conjugate read on the constraint.

- **Residue** — the **duality gap**, tagged **`q=+1`**. What the conjugate-reading forces but does not
  capture is the gap `f − f**` (resp. `min_x − max_λ`): `clo(f) = f**` is the **closed convex hull**
  (`adjunction.md`'s `clo_extensive`: `f** ≤ f` always — the unit/over-shoot direction; the gap is the
  surplus). **Strong duality** (Slater) is the residue *vanishing* — `f = f**`, the closure being the
  identity, exactly `galois.md`'s "fundamental theorem = residue-collapse-to-closure on the closed
  elements." The gap settles to a fixed point (`clo` idempotent, `q=+1`), never oscillates — convex
  duality lives on the **same `q=+1` converging pole** as φ/Gaussian/ODE, not the Cantor `q=−1` escape.

## Re-seeing — `⟨C | L⟩ ⊕ Residue`

```
   convex function f       =  ⟨ point-construction ∣ second-difference ≥ 0 ⟩      (height read twice, nonneg)
   convexity (Hessian PSD)  =  the symmetric operator's disc ≥ 0                    (Mat2SymmetricSpectrum, q=+1)
   Legendre transform f*    =  ⟨ functions ∣ the order-reversing conjugate sup_x(px−f) ⟩   = galois.md's Fix
   biconjugate f**          =  clo(f) = (·)*∘(·)*  = the closed convex hull         (adjunction.md's T=G∘F)
   f** = f  (convex closed)  =  clo_idempotent / residue-collapse                    (galois.md's fundamental thm)
   Lagrangian L(x,λ)        =  the conjugate's pairing internalised on a constraint
   weak duality  max_λ min_x L  ≤  min_x max_λ L   =  the adjoint inequality        (gc_unit: a ≤ g(f a))
                             =  Kantorovich:  dualValue ≤ transportCost              (kantorovich_weak_duality)
   strong duality (Slater)   =  the gap = 0  =  closure exact  =  "they meet"        (ollivier_plan_optimal)
   THE MINIMUM              =  Residue(L,C), q=+1  =  gradient flow's fixed point    (gradient_descent_monotone)
   KKT / 0 ∈ ∂f(x*)         =  the q=+1 stationary residue: step x* = x*            (IsNormalForm, conceptual obj)
   non-convex / gap > 0      =  closure ≠ id off the closed elements (residue survives)
```

The map is exact: **`galois.md`'s `Fix ⊣ Inv` with `clo = Inv∘Fix` is the Legendre–Fenchel transform
with `clo = f↦f**`**. Convexity is what makes the closure *trivial* (`f** = f`), the same way a normal
extension makes the Galois closure trivial. Off the convex/closed locus the closure is a proper
contraction `f** ≤ f` (the convex hull strictly below `f`), and the surplus is the duality gap.

## LEVERAGE — does convex duality fall out as `galois.md`'s closure?

**Verdict: PREDICTION (the strongest consolidation in the notebook) — with one real PARTIAL, the
*transform object itself* absent, located precisely.** Convex duality is not a new field; it is the
**single `q=+1` adjoint-closure object read on functions**, and it ties together four prior entries
that were not previously known to be one. Four legs, honestly graded.

**(A) Legendre–Fenchel = `galois.md`'s order-reversing adjunction; `f** = clo(f)` = the convex hull —
PREDICTED, abstractly grounded, the transform object conceptual.** Before any Lean: the conjugate
`f*(p) = sup_x(px − f(x))` is order-reversing (`f ≤ g ⟹ g* ≤ f*`) and `f ↦ f*` composed with itself
is **extensive, monotone, idempotent on closed functions** — i.e. it *is* a closure operator. The
calculus says: any order-reversing self-map of a lattice generates `clo = (·)*∘(·)*` with the laws
`adjunction.md` proved as `clo_extensive` (here `f** ≤ f`, the unit), `clo_monotone`, and
`clo_idempotent` (`f*** = f*`, so `f**** = f**` — the closed convex hull is closed). **The repo proves
this closure abstractly** (`Order/GaloisConnection.lean`: `clo`, `clo_extensive`, `clo_monotone`,
`clo_idempotent`, `gc_fgf`/`gc_gfg`, all PURE) and `adjunction.md` already identified it as *the*
idempotent monad of an adjoint pair. So the structural claim — "`f** = clo(f)` = the closed convex hull,
the Galois closure of the conjugate-reading; `f** = f` (Fenchel–Moreau) is the residue-collapse on the
closed/convex elements" — is **grounded as a general order fact**, not asserted. *Conceptual leg:* the
**`sup_x` Legendre-transform object `f*` itself is not built** — there is no `convexConjugate`,
`epigraph`, or `biconjugate` in the repo (grep: zero hits for a real convex-conjugate object; every
`convex` hit is Jensen-convexity of the square in the heat equation, every `conjugate` hit is
complex/algebraic conjugation). The closure *machine* is present and certified; the *function-lattice
instantiation* `clo = (·)*` is conceptual — exactly `galois.md`'s "field-theoretic instance missing,
the structure it inhabits present."

**(B) Weak duality = the adjoint inequality; strong duality = the gap-zero closure — PREDICTED AND
GROUNDED (the surprise).** The minimax inequality `max_λ min_x L(x,λ) ≤ min_x max_λ L(x,λ)` is exactly
`adjunction.md`'s `gc_unit`/`gc_counit` (the over-shoot/under-shoot of an adjoint pair: `a ≤ g(f a)`,
`f(g b) ≤ b`). The calculus predicts this is *one inequality*, and the repo **already proves a concrete
∅-axiom instance**: `OllivierRicci.kantorovich_weak_duality` — for a transport plan `π ≥ 0` and a
1-Lipschitz potential `f`, `dualValue f π ≤ transportCost d π`, i.e. the **`W₁`-dual ≤ `W₁`-primal**
direction of Kantorovich/LP duality. This *is* weak duality (`sup over potentials ≤ inf over plans`),
worked over ℤ via the grid-sum/Fubini toolkit. And **strong duality / the zero duality gap is also
built**: `ollivier_plan_optimal` is the optimality certificate — *when a plan and a potential **meet***
(`dualValue f π = transportCost d π`, the gap = 0), the plan is cost-optimal among all plans with its
marginals, so `W₁` is *pinned* exactly. That "they meet ⟹ optimal" is precisely **strong duality =
the closure being exact = the residue vanishing**, and `ollivier_bracket` is the squeeze
`1 − transportCost ≤ 1 − dualValue` = the gap as a bracket the residue lives in. This is the leg I
expected to be conceptual and is instead a **real ∅-axiom weak-duality + zero-gap theorem** — the
strongest grounding in the entry.

**(C) Convexity = the `q=+1` PSD-Hessian corner — PREDICTED, grounded on the matrix shadow.** The
calculus says convexity = the second-order/curvature reading being `≥0`, and `spectral.md`'s det/tr
dissolution gives the test: a symmetric (self-adjoint, Hessian-shaped) operator has **real,
sign-determined spectrum iff `disc ≥ 0`**, and the symmetric case forces it —
`Mat2SymmetricSpectrum.disc_symmetric_nonneg` (`0 ≤ disc M` for `IsSymmetric M`), bundled in
`symmetric_spectrum_real`. This is *the* `q=+1` real-nonneg-spectrum corner: convex ⟺ the Hessian's
spectrum is real and nonneg ⟺ the symmetric `disc ≥ 0`. *Grounded at `2×2`*; the conceptual leg is the
general `n×n` PSD-Hessian and the convexity-of-`f`-from-PSD-Hessian implication (the repo has the
spectral corner, not a multivariate convex-function-from-Hessian theorem).

**(D) The minimum = gradient flow's `q=+1` fixed point; KKT = the stationary residue — PREDICTED,
the descent grounded, the subgradient object conceptual.** `differential_equations.md`'s gradient flow
is the `q=+1` Lyapunov descent: `GradientFlow.gradient_descent_monotone` (`F(x−τ∇F) ≤ F(x)` for
`0≤τ≤1`) with the exact identity `gradient_descent_identity` (`F(x−τ∇F) = F(x) − τ(1−τ)‖∇F‖²`, the
discrete `d/dt F = −‖∇F‖² ≤ 0`). The minimum of a convex `f` is the **fixed point this descent reaches**
(`MonovariantFlow.flow_reaches` / `IsNormalForm f x* := f x* = x*`, the degenerate `q=+1` residue:
`step x* = x*` ⟺ `∇F(x*) = 0`). **KKT / `0 ∈ ∂f(x*)`** is exactly this stationarity — the gradient (or
subgradient) vanishing at the fixed point — which is *why* the descent stops there. *Conceptual leg:*
the **subgradient/subdifferential `∂f` object is absent** (grep: no `subgradient`/`subdifferential`);
the *smooth* stationary point `∇F = 0` is the grounded shadow (`gradient_descent_identity`'s
`‖∇F‖² = 0` zero-deficit fixed point), the set-valued `∂f` for non-smooth convex `f` is the named gap.

**Net.** Not collapse-only (it **predicts** the form of all four pillars from the four prior entries and
*derives why*: convexity is `q=+1` PSD, the minimum is the `q=+1` descent fixed point, weak duality is
the adjoint inequality, strong duality is the closure being exact, the gap is the closure residue).
Not a miss (the adjunction/closure laws, a real Kantorovich weak-duality + zero-gap certificate, the
symmetric-PSD corner, and the gradient-descent identity are **all ∅-axiom theorems**). It is a
**prediction whose every structural leg is grounded and whose three missing legs are *named objects*
(`f*`/`f**`, `∂f`, the LP saddle `L(x,λ)`), not missing structure** — the structure they would inhabit
(`clo`, the adjoint inequality, the `q=+1` fixed point) is wholly present.

## Revelation

**Convex duality is ONE `(C,L)` — `galois.md`'s order-reversing adjoint-closure read on functions —
and it consolidates FOUR prior entries into one object.** This is a **collapse + forcing + residue-
surfaced**, three at once, and the deepest consolidation the notebook has produced:

1. **Collapse — the four pillars are one adjunction.** The Legendre–Fenchel transform (`f↦f*`), weak
   duality (`max min ≤ min max`), strong duality (gap = 0), and the Fenchel–Moreau biconjugate
   (`f** = f`) are **not four theorems** — they are the `clo = G∘F` closure of `adjunction.md`'s
   idempotent monad, read on the function lattice: `f*` = the order-reversing adjoint, `f** = clo(f)` =
   the convex hull, weak duality = `gc_unit`/`gc_counit`, strong duality = `clo` exact on the closed
   (convex) elements = `galois.md`'s fundamental theorem (residue-collapse-to-closure). **The duality
   gap IS the closure residue** `f − clo(f)`.

2. **Forcing — convexity is forced as the `q=+1` corner, the minimum as the `q=+1` fixed point.**
   Convexity is *not an arbitrary hypothesis*: it is the second-order reading being `≥0` =
   `spectral.md`'s symmetric `disc ≥ 0` = the real-nonneg-spectrum `q=+1` pole (`disc_symmetric_nonneg`).
   And it is *exactly* the condition under which gradient descent converges to a unique fixed point —
   the `q=+1` contraction residue of `differential_equations.md` (`gradient_descent_monotone`,
   `IsNormalForm`). So **convexity = `q=+1` is the same bit twice**: PSD curvature (the closure settles,
   no gap) and descent convergence (the minimum is reached, no escape). Non-convexity is the `q=−1`
   escape — multiple basins, a positive gap, the closure not the identity.

3. **Residue surfaced — strong duality is the gap *vanishing*, not a miracle.** Classical convex
   analysis states strong duality as a *theorem under Slater's condition*; the calculus re-sees it as
   the **residue collapsing on the closed elements** — the same shape as Galois normality and Carathéodory's
   conservative extension (`measure.md`). The duality gap stops being a quantity to bound and becomes
   `clo(f)` vs `f`: zero exactly on the convex-closed locus, and the `q=+1` tag guarantees it *settles*
   (idempotent closure) rather than escaping (no diagonal — there is always a saddle on the closed locus).

**THE CONSOLIDATION (the brief's central question):** convex duality is the meeting point of the
notebook's two load-bearing invariants — the **adjoint-closure** (`galois`/`adjunction`, `q=+1` settle)
and the **`q=+1` fixed point** (`differential_equations`/`spectral`):

| pillar | 213 reading | prior entry | Lean status |
|---|---|---|---|
| Legendre–Fenchel `f*`, `f**` | order-reversing conjugate; `f**=clo(f)`=convex hull | `galois.md` / `adjunction.md` | closure **built** (`clo_idempotent`); transform object conceptual |
| weak duality `max min ≤ min max` | the adjoint inequality `gc_unit`/`gc_counit` | `adjunction.md` | **built** (`kantorovich_weak_duality`, Kantorovich/LP) |
| strong duality (Slater) | the gap = 0 = closure exact = "they meet" | `galois.md` (fundamental thm) | **built** (`ollivier_plan_optimal`, `ollivier_bracket`) |
| convexity (Hessian PSD) | second-order ≥0 = symmetric `disc ≥ 0`, `q=+1` real spectrum | `spectral.md` | **built** at 2×2 (`disc_symmetric_nonneg`) |
| the minimum | gradient flow's `q=+1` fixed point `∇F=0` | `differential_equations.md` | descent **built** (`gradient_descent_monotone`); `∂f` conceptual |
| KKT / `0 ∈ ∂f(x*)` | the `q=+1` stationary residue `step x*=x*` | `differential_equations.md` | smooth `∇F=0` **built** (`IsNormalForm`); subgradient conceptual |
| duality gap | the closure residue `f − clo(f)`, `q=+1` (settles) | `galois.md` / `ResidueTag` | **built** as a residue concept |

So **YES** — Legendre–Fenchel duality falls out as `galois.md`'s order-reversing closure
(`f** = clo(f)` = convex hull, the duality gap = the closure residue), **convexity is the `q=+1`
PSD-Hessian corner** (`Mat2SymmetricSpectrum`), and **the minimum is gradient-flow's `q=+1` fixed
point** (`GradientFlow`/`MonovariantFlow`). Convex duality is one object read across the adjoint-closure
and the `q=+1` fixed point — it consolidates `galois` + `adjunction` + `differential_equations` +
`spectral` with **no new axis**.

## Note for the technique — does convex duality force a new construct?

**Verdict: EXTEND by consolidation — no new primitive.** Every slot convex duality uses already exists:
- **the order-reversing adjoint pair → closure** (`galois.md`/`adjunction.md`'s `clo`) — the
  Legendre–Fenchel transform is its function-lattice instance;
- **the `q=+1` PSD / real-nonneg-spectrum corner** (`spectral.md`) — convexity;
- **the `q=+1` gradient-descent fixed point** (`differential_equations.md`) — the minimum / KKT
  stationarity;
- **the adjoint inequality `gc_unit`/`gc_counit`** — weak duality (with a real LP instance,
  Kantorovich);
- **the `q=±1` residue tag** (`ResidueTag.lean`) — the duality gap (`q=+1`, settles to zero on the
  convex-closed locus).

The one sharpening: **convexity is the condition that makes BOTH `q=+1` legs fire at once** — the
closure becomes exact (no duality gap) *and* the descent converges (the minimum is reached). The
calculus thus predicts the classical fact "convex ⟹ strong duality + global minimum" as **one
condition (`q=+1`) read two ways** (closure exact + contraction converges), not two separate theorems.

## Verified Lean anchors (file:theorem:line — all grep-verified; purity by `tools/scan_axioms.py`)

| Leg | Theorem (file : name : line) | Status |
|---|---|---|
| `f** = clo(f)` = convex hull; Fenchel–Moreau = residue-collapse; the **closure machine** (shared with Galois) | `Lib/Math/Order/GaloisConnection.lean : clo` (`:104`), `clo_extensive` (`:107`, `f**≤f` unit), `clo_monotone` (`:114`), `clo_idempotent` (`:126`, `f***=f*`), `gc_unit` (`:41`), `gc_counit` (`:49`), `gc_fgf` (`:79`), `gc_gfg` (`:91`) | ∅-axiom ✓ (15 pure / 0 dirty) |
| **weak duality `max_λ min_x ≤ min_x max_λ`** = the adjoint inequality (real Kantorovich/LP instance) | `Lib/Math/Geometry/DiscreteCurvature/OllivierRicci.lean : kantorovich_weak_duality` (`:52`, `dualValue ≤ transportCost`), `dualValue` (`:40`), `transportCost` (`:36`) | ∅-axiom ✓ (31 pure / 0 dirty) |
| **strong duality (Slater)** = the gap = 0 = closure exact ("they meet") + the gap-bracket | `OllivierRicci.lean : ollivier_plan_optimal` (`:106`, `dualValue=transportCost ⟹ optimal`), `ollivier_bracket` (`:91`, `1−cost ≤ 1−dual`) | ∅-axiom ✓ (same module) |
| **convexity = Hessian PSD = `q=+1` real-nonneg spectrum** | `Lib/Math/NumberSystems/Real213/Mat2/Mat2SymmetricSpectrum.lean : disc_symmetric_nonneg` (`:83`, `0≤disc` for symmetric), `symmetric_spectrum_real` (`:137`), `IsSymmetric` (`:52`) | ∅-axiom ✓ (9 pure / 0 dirty) |
| **the minimum = gradient flow's `q=+1` fixed point** (Lyapunov descent) | `Lib/Math/Analysis/Optimization/GradientFlow.lean : gradient_descent_monotone` (`:138`, `F(x−τ∇F)≤F(x)`), `gradient_descent_identity` (`:128`, `=F(x)−τ(1−τ)‖∇F‖²`) | ∅-axiom ✓ (9 pure / 0 dirty) |
| **KKT / stationarity = the degenerate `q=+1` residue** `∇F=0 ⟺ step x*=x*` | `Lib/Math/Foundations/MonovariantFlow.lean : flow_reaches` (`:99`), `IsNormalForm` (`:73`) | ∅-axiom ✓ (referenced via `differential_equations.md`, 19/0) |

> Axiom-purity note: `GaloisConnection`, `OllivierRicci`, `Mat2SymmetricSpectrum`, and `GradientFlow`
> were re-run through `tools/scan_axioms.py` from repo root this session — **93 pure / 0 dirty** across
> the four modules (15 + 31 + 9 + 9 + the OllivierRicci defs), every cited theorem PURE.

## Conceptual-only legs (honest — NOT grounded in repo Lean; the located missing primitive)

- **The Fenchel–Moreau weld `f**=clo(f)` — NOW GROUNDED at the abstract level** (`Order/FenchelMoreau.lean`,
  18/0 PURE): the Legendre transform is *antitone* (order-reversing) and self-adjoint, which the repo's
  *monotone* `clo` did not express — so the agent built the antitone-self-adjoint closure and welded it.
  `cloAntitone star x := star (star x)`; `biconjugate_eq_clo` (`f**=clo f`); `cloAntitone_extensive`
  (**weak duality** `x ≤ star(star x)`, the gap = the residue); `star_triple` (`f***=f*`);
  `biconj_idempotent` (**Fenchel–Moreau `f****=f**`**); `closed_iff_fixed` (**strong duality**: the residue
  vanishes exactly on the closure-fixed/"convex" locus, q=+1); and the precise reduction
  `cloAntitone_eq_gc_clo` (the antitone `star` IS a monotone Galois connection `star⊣star` into the order-dual,
  so `cloAntitone star = GaloisConnection.clo star star` by `rfl`). Bool order-reversal witnesses the convex
  `f**=f` corner. So convex_duality.md's named weld ("instantiate the closure at `Fix=Inv=(·)*`") is
  satisfied for any order-reversing involution.
- **Residual — the actual `sup_x(px−f(x))` Legendre transform OBJECT** — still absent (needs `Real213`: a
  sup over a real function-lattice; `convexConjugate`/`epigraph` unbuilt). The closure *machine* (now both
  monotone and antitone) is certified; only the real-valued `sup` transform instance is unwritten — the
  precise remaining missing leg, parallel to `galois.md`'s missing field-extension and `knots.md`'s boundary.
- **The convex function as a typed object** — convexity exists only as Jensen inequalities on specific
  expressions and as the symmetric `disc≥0` matrix shadow; there is no `Convex (f : ℝ → ℝ)` predicate
  or `f'' ≥ 0` theorem. The `q=+1` PSD corner is grounded at `2×2`; the multivariate
  convex-from-PSD-Hessian implication is conceptual.
- **The subdifferential `∂f` / KKT conditions as named objects** — **absent.** The grounded shadow is
  the smooth stationary point `∇F = 0` (`gradient_descent_identity`'s zero-deficit fixed point,
  `IsNormalForm`); the set-valued subgradient `0 ∈ ∂f(x*)` for non-smooth convex `f`, and a named
  KKT-system theorem, are the missing objects.
- **The Lagrangian saddle `L(x,λ) = f(x)+⟨λ,g(x)⟩` and the `min_x max_λ` saddle-point theorem** —
  not built *as a Lagrangian*. The **weak-duality and zero-gap content is grounded** in the Kantorovich
  LP instance (`OllivierRicci`), which is a genuine `sup_dual ≤ inf_primal` with a "they meet" strong-
  duality certificate; the *general* Lagrangian-with-constraints saddle object is conceptual (the LP
  instance is the one realised case, the way `mulDiv_gc` is `galois.md`'s one realised numeric adjunction).
- **Slater's condition / constraint qualification** — absent as a named hypothesis; the grounded analogue
  is "a plan and a potential meet" (`ollivier_plan_optimal`'s `hmeet`), which *is* zero-gap, but the
  general constraint-qualification ⟹ zero-gap theorem is conceptual.

## Verdict: PREDICTION (consolidating galois + adjunction + gradient-flow + spectral), one PARTIAL

Convex duality **predicts and consolidates** — it does not break the model and adds no axis. The
load-bearing claims are all grounded ∅-axiom: the **closure machine** (`clo_idempotent` = `f**`'s
idempotence = Fenchel–Moreau), a **real weak-duality + zero-gap theorem** (`kantorovich_weak_duality`,
`ollivier_plan_optimal` — better than expected, the leg I forecast as conceptual is built), the
**`q=+1` PSD corner** (`disc_symmetric_nonneg` = convexity), and the **`q=+1` descent fixed point**
(`gradient_descent_monotone` = the minimum / KKT stationarity). The one PARTIAL is the **Legendre–Fenchel
transform object `f*`/`f**` itself** (with `∂f` and the general Lagrangian saddle) — absent, located
precisely: the closure *structure* it inhabits is present and certified, only the function-lattice
*instance* is unwritten, exactly as `galois.md` located its missing field-extension instance.

> **Open Lean target the calculus names precisely:** define `convexConjugate (f) (p) := sup_x (p·x − f x)`
> on a `Real213`/dyadic function-lattice, show `(·)*` is order-reversing, and instantiate
> `Order/GaloisConnection.clo` at `Fix = Inv = (·)*` to obtain `f** = clo f` with `clo_idempotent`
> giving Fenchel–Moreau (`f*** = f*`) and `clo_extensive` giving `f** ≤ f` — the **Legendre–Fenchel
> transform as the function-lattice instance of `galois.md`'s closure**, the one weld that would promote
> this entry from PREDICTION+PARTIAL to a closed derivation (parallel to `ConvolveRescaleContraction`
> welding the Banach engine to the CLT).
