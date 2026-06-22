# Decomposition: optimal transport (Monge–Kantorovich, the LP relaxation, Kantorovich–Rubinstein duality, W₁, the c-transform / c-concavity, Brenier)

*213-decomposition of optimal transport, per `../README.md` (model v7.1: `OBJECT = ⟨C | L⟩ ⊕
Residue(L,C)`). The bar is **leverage / consolidation, not re-skin**. Hypothesis under test: optimal
transport is the calculus's **weight-axis transport read through the `f**=clo` duality** — the
Kantorovich LP is the weight axis (`mass_conv`/`momentNum_conv`) with an LP duality already grounded
(`kantorovich_weak_duality`), and Kantorovich–Rubinstein duality is the **SAME** Legendre–Fenchel
`f**=clo` biconjugation (`FenchelMoreau`), making OT the **fourth instance of the order-reversing
closure family** after Galois / Legendre–Fenchel / Nullstellensatz (SYNTHESIS §2). It consolidates
`convex_duality.md` (the `f**=clo` closure + the very `kantorovich_weak_duality` it already cites),
`measure.md` / `probability.md` (the weight axis), and `ResidueTag.lean` (the q=±1 tag).*

This is the rare entry whose **load-bearing legs are already ∅-axiom in the repo** — the Kantorovich
LP weak-duality, the zero-gap optimality certificate, and the `f**=clo` closure are all built and
PURE. The **named OT objects** (`Wasserstein`, `OptimalTransport`, `Monge`, `cTransform`, `Brenier`)
are **absent** — grep-confirmed — and located precisely.

## The decomposition (C / Reading / Residue)

- **Construction `C`** — a construction with a **weight** sub-structure (`README` model v3: `L` carries
  a `weight`; `probability.md`/`measure.md`): a *value-weighted count*. The objects OT talks about are
  **measures** `μ, ν` — `measure.md`'s weight-reading run before the ratio fold, i.e. a mass
  distribution over a point-construction with a cost/distance `d(x,y)` between points (the difference
  reading `L₋` lifted to a pairing). A **transport plan / coupling** `π` is a *joint* weight on pairs
  `(x,y)` whose **marginals** are `μ` and `ν` (`rowMarg`/`colMarg` in the Lean: `μ x = Σ_y π x y`,
  `ν y = Σ_x π x y`). The coupling is the weight-axis's *joint* form — the same `weight` slot the
  convolution `⋆` uses (`mass_conv`: total mass multiplicative; `momentNum_conv`: mean additive).

- **Reading `L`** — **two readings of one weighted construction, bound by the `f**=clo` order-reversing
  closure.**
  1. The **primal** (Monge–Kantorovich) reading is the weight-axis **cost**: `transportCost d π =
     Σ_x Σ_y d(x,y)·π(x,y)` — a value-weighted count over the joint weight, exactly the linear
     functional the weight axis reads. The Monge problem is the **deterministic** sub-case (π
     supported on a graph `y = T(x)`); the **Kantorovich LP relaxation** is the *same* reading over
     the *full* convex set of couplings — relaxing "a map" to "a joint weight" is moving from a point
     of the weight-simplex to the whole simplex, no new primitive.
  2. The **dual** (Kantorovich–Rubinstein) reading is the **Legendre–Fenchel conjugate of the cost**,
     read on potentials: `dualValue f π = Σ_x f(x)·μ(x) − Σ_y f(y)·ν(y)` over `1`-Lipschitz `f`. The
     **c-transform** `f^c(y) = inf_x (c(x,y) − f(x))` *is* the c-Fenchel conjugate — `convex_duality.md`'s
     order-reversing `(·)*` with the linear pairing replaced by the cost `c`; **c-concavity** = the
     **closed/fixed points of the conjugation closure** `f = f^{cc}` = `FenchelMoreau.closed_iff_fixed`.
     W₁(μ,ν) = `sup` over `1`-Lipschitz `f` of `∫ f d(μ−ν)` is the biconjugate evaluation, the SAME
     `f**=clo` arrow as Galois `Fix∘Inv` and Legendre `(·)*∘(·)*` (`biconjugate_eq_clo`,
     `biconj_idempotent`).

- **Residue** — the **duality gap** `transportCost − dualValue ≥ 0`, tagged **`q = ±1`**. The
  conjugate-reading forces the gap (`cloAntitone_extensive`: `x ≤ star(star x)` always — the unit /
  over-shoot). **`q = +1`** = the gap *vanishes*: a plan `π` and a potential `f` **meet**
  (`dualValue = transportCost`), the closure is exact, `W₁` is pinned, the coupling is optimal
  (`ollivier_plan_optimal`). This is the converging/settle pole — strong duality = no gap = the
  residue-collapse-to-closure (`galois.md`'s fundamental theorem, `closed_iff_fixed`). **`q = −1`** =
  the gap *survives* (non-tight: the closure is a proper contraction off its closed locus — a cost
  with no Kantorovich potential achieving the sup, the escape pole). Brenier's theorem (the optimal
  map = `∇` of a convex potential) is the `q=+1` corner made geometric: the c-concave potential is
  `clo`-fixed (`closed_iff_fixed`), and its gradient is `convex_duality.md`'s gradient-of-the-convex
  potential (`GradientFlow`/`gradient_descent_identity`'s `∇F` fixed point).

## Re-seeing — `⟨C | L⟩ ⊕ Residue`

```
   measure μ, ν             =  ⟨ point-construction ∣ weight (value-weighted count) ⟩   (measure.md)
   transport plan / coupling π =  ⟨ pairs ∣ joint weight with marginals μ, ν ⟩          (rowMarg/colMarg)
   Monge map T              =  the deterministic π (supported on y=T(x)) — a point of the simplex
   Kantorovich LP           =  the SAME cost-reading over the FULL coupling simplex (relaxation)
   transport cost (primal)  =  Σ_x Σ_y d(x,y)·π(x,y)  =  the weight-axis cost functional   (transportCost)
   c-transform f^c          =  the c-Fenchel conjugate  =  galois.md's order-reversing (·)*   (cloAntitone)
   c-concavity  f = f^{cc}  =  the closed/fixed points of the closure                       (closed_iff_fixed)
   W₁ = sup_{1-Lip f} ∫f d(μ−ν) =  the biconjugate f** = clo(f)                              (biconjugate_eq_clo)
   Kantorovich–Rubinstein duality (sup_f = inf_π) = the f**=clo biconjugation, 4th instance  (biconj_idempotent)
   weak duality  dualValue ≤ transportCost  =  the adjoint inequality / clo unit            (kantorovich_weak_duality)
   strong duality / NO gap (they meet) =  closure exact = residue collapse, q=+1            (ollivier_plan_optimal)
   the duality GAP (nonzero, non-tight) =  Residue(L,C), q=−1 (closure ≠ id, contraction)   (cloAntitone_extensive)
   Brenier T = ∇(convex potential) =  the q=+1 gradient of the clo-fixed potential          (GradientFlow, conceptual weld)
```

The map is exact at the **same place `convex_duality.md` lands**: `kantorovich_weak_duality`
*is* `convex_duality.md`'s weak-duality leg (the calculus already cited it there), and
`ollivier_plan_optimal` *is* its strong-duality / zero-gap leg. The NEW datum here is that **W₁'s
Kantorovich–Rubinstein duality `sup_f = inf_π` is the `f**=clo` biconjugation on the transport cost** —
the c-transform `f^c` = the conjugate, c-concavity `f=f^{cc}` = `closed_iff_fixed`, putting OT in the
**order-reversing closure family alongside Galois / Legendre / Nullstellensatz**, the family SYNTHESIS
§2 names as "three instances of one `clo_idempotent`/`biconj_idempotent`". OT is the **fourth**.

## LEVERAGE — does OT fall out as the weight axis read through `f**=clo`?

**Verdict: EXTEND by consolidation — no new axis, the load-bearing legs already ∅-axiom — with one
PARTIAL: the named OT objects (`Wasserstein`/`Monge`/`cTransform`/`Brenier`) absent, the
measure-coupling primitive present only as the finite-ℤ `OllivierRicci` instance.** Five legs, honestly
graded.

**(A) The Kantorovich LP cost = the weight-axis cost functional — GROUNDED.** `transportCost d π =
Σ_x Σ_y d(x,y)·π(x,y)` is literally the value-weighted count of `measure.md`/`probability.md`, with
`rowMarg`/`colMarg` the marginals that make `π` a coupling. The relaxation from Monge (a map) to
Kantorovich (a joint weight) is the move from a vertex of the coupling-simplex to its interior — the
weight axis already hosts the simplex (`mass_conv`/`momentNum_conv` on `ConvolveProfile` are the
convolution = independent-coupling case). **The transport primitive is built** over ℤ on a finite index
set `{0,…,n−1}` (`OllivierRicci`, `gridSumZ`/Fubini). The conceptual leg: a *general* measure-coupling
object over an arbitrary base (the σ-algebra-free `DyadicMeasure` exists, but the coupling
`rowMarg`/`colMarg` machinery lives only in the finite-ℤ `OllivierRicci`).

**(B) Weak duality `dualValue ≤ transportCost` = the adjoint inequality / `clo` unit — GROUNDED
∅-axiom.** `kantorovich_weak_duality` (OllivierRicci.lean:52, PURE) proves `dualValue n f π ≤
transportCost n d π` for `π ≥ 0` and `1`-Lipschitz `f`, worked via the marginals + Fubini sum-swap +
termwise bound. This **IS** the `sup_f ≤ inf_π` half of Kantorovich–Rubinstein, and it is exactly
`convex_duality.md`'s weak-duality leg (`gc_unit`/`cloAntitone_extensive`: `x ≤ star(star x)`). The
calculus predicts one inequality; the repo proves the OT instance of it. **The strongest grounding in
the entry — the duality core of OT is a committed ∅-axiom theorem.**

**(C) Strong duality / zero gap (Kantorovich–Rubinstein `sup_f = inf_π`) = the closure exact / residue
collapse — GROUNDED ∅-axiom.** `ollivier_plan_optimal` (OllivierRicci.lean:106, PURE): when a plan and
a `1`-Lipschitz potential **meet** (`dualValue f π = transportCost d π`, the gap = 0), `π` is
cost-optimal among **all** plans sharing its marginals, so `W₁ = transportCost d π` exactly. That
"they meet ⟹ optimal" is **strong duality = the closure being exact on the closed (c-concave) locus =
`closed_iff_fixed`**, the same residue-collapse as Galois normality and Carathéodory's conservative
extension. `ollivier_bracket` (OllivierRicci.lean:91, PURE) is the gap as a squeeze bracket
`1−cost ≤ 1−dual` — the residue lives in it.

**(D) Kantorovich–Rubinstein W₁ = the `f**=clo` biconjugation; the c-transform = the conjugate;
c-concavity = the closed/fixed points — GROUNDED at the abstract closure, the c-transform object
conceptual.** The c-transform `f^c(y) = inf_x(c(x,y) − f(x))` is order-reversing in `f` and
self-companion under the cost pairing, so `f ↦ f^c` generates the closure `clo(f) = f^{cc} =
(·)^c∘(·)^c`. The repo proves this closure **abstractly** for any order-reversing involution
(`FenchelMoreau.lean`, 18/0 PURE): `cloAntitone star x = star(star x)` (`biconjugate_eq_clo`:59),
`cloAntitone_extensive` (:72, weak duality `x ≤ star(star x)`), `star_triple` (:109, `f^{ccc}=f^c`),
`biconj_idempotent` (:134, **Fenchel–Moreau** `f^{cccc}=f^{cc}`), `closed_iff_fixed` (:152, **strong
duality / c-concavity**: the gap vanishes exactly on the closure-fixed locus, q=+1), and the precise
reduction `cloAntitone_eq_gc_clo` (:187, the antitone `star` IS a monotone Galois connection into the
order-dual, `= GaloisConnection.clo star star` by `rfl`). **So W₁'s Kantorovich–Rubinstein duality is
the SAME idempotent closure as Galois / Legendre / Nullstellensatz** — the fourth instance, the new
datum. *Conceptual leg:* the actual `inf_x(c(x,y)−f(x))` c-transform OBJECT is not built (needs a
`Real213`/dyadic function-lattice `inf`); the closure *machine* is certified, only the cost-pairing
instance is unwritten — exactly `convex_duality.md`'s located missing `sup_x(px−f)` Legendre object.

**(E) Brenier's theorem (optimal map = `∇` convex potential) = the `q=+1` gradient of the clo-fixed
potential — PREDICTED, the descent grounded, the map object conceptual.** Brenier's potential is
c-concave (`closed_iff_fixed`, q=+1) and its gradient is the optimal map. `convex_duality.md`'s
gradient leg is grounded: `GradientFlow.gradient_descent_monotone`/`gradient_descent_identity` give the
`q=+1` descent to `∇F=0` (`MonovariantFlow.IsNormalForm`). So Brenier = the `q=+1` fixed-point structure
already built, read on the cost potential. *Conceptual leg:* the convex-potential-as-typed-object and
the `∇φ`-pushforward-equals-optimal-map theorem are absent (no `Brenier`, no `convexConjugate`), the
same gap `convex_duality.md` flags.

**Net.** Not collapse-only and not a re-skin of `convex_duality.md`: the **NEW** structural claim is
that OT's Kantorovich–Rubinstein W₁-duality is the `f**=clo` closure read on the **transport cost over
measures** — the FOURTH instance of the order-reversing closure family — with the weight axis supplying
the coupling/cost and `FenchelMoreau` supplying the biconjugation. Two of OT's load-bearing legs (weak
duality, zero-gap optimality) are committed ∅-axiom theorems the corpus already had; the third (the
biconjugation) is the abstract closure, certified. The honest residual is the **named OT object layer**
(`Wasserstein`/`Monge`/`cTransform`/`Brenier`) and a **general measure-coupling primitive** beyond the
finite-ℤ `OllivierRicci` instance.

## Revelation

**Optimal transport is ONE `(C,L)` — the weight axis read through the `f**=clo` order-reversing
closure — and it is the FOURTH instance of the closure family (Galois / Legendre / Nullstellensatz /
optimal transport).** This is **collapse + forcing + residue-surfaced**, three at once:

1. **Collapse — Kantorovich–Rubinstein W₁-duality IS the `f**=clo` biconjugation, the fourth instance.**
   The c-transform `f^c` (the c-Fenchel conjugate), c-concavity `f=f^{cc}`, and W₁ `= sup_{1-Lip}∫f
   d(μ−ν)` are **not OT-specific objects** — they are `FenchelMoreau`'s order-reversing closure
   `cloAntitone star x = star(star x)` with `star = (·)^c` (the conjugate against the cost pairing):
   `f^c` = the antitone adjoint, W₁ = `biconjugate_eq_clo`, c-concavity = `closed_iff_fixed`, Fenchel–
   Moreau = `biconj_idempotent`. SYNTHESIS §2 named **three** instances of one idempotent closure
   (`clo_idempotent`/`biconj_idempotent`); OT is the **fourth**, sharing the exact Lean object.

2. **Forcing — the Kantorovich LP is forced as the weight axis, the duality as its adjoint.** The LP is
   not an arbitrary relaxation: it is the weight-axis cost functional `Σ d·π` over the coupling-simplex
   (`transportCost`, `rowMarg`/`colMarg`), and its dual is *forced* to be the conjugate-reading on
   potentials — weak duality is the closure unit (`kantorovich_weak_duality` = `cloAntitone_extensive`),
   so `dualValue ≤ transportCost` is `x ≤ star(star x)` read on the transport cost. The duality is the
   adjoint inequality, not a separate theorem.

3. **Residue surfaced — the duality gap is the q=±1 closure residue, not a quantity to bound.** Strong
   duality stops being "a theorem under regularity" and becomes the **residue collapsing on the
   c-concave (closed) locus**: gap = 0 ⟺ `closed_iff_fixed` ⟺ a plan and a potential meet
   (`ollivier_plan_optimal`), the `q=+1` settle pole; a surviving non-tight gap is the `q=−1` escape
   (closure a proper contraction, no achieving potential). The `ResidueTag` `±1` bit
   (`residue_tag_two_poles`, 55/0) now also reads "tight transport duality (q=+1) vs gap (q=−1)",
   alongside Cantor/φ/Gödel/measure/convex-duality.

**THE CONSOLIDATION:** OT is the meeting of two corpus invariants — the **weight axis**
(`measure.md`/`probability.md`, `mass_conv`/`momentNum_conv`) and the **`f**=clo` closure**
(`convex_duality.md`/`galois.md`, `biconj_idempotent`) — bound by the **q=±1 residue** (the gap). The
spine row for SYNTHESIS §3: **tight transport duality (`ollivier_plan_optimal`, q=+1)** vs **non-tight
gap (q=−1)** sits with convex duality's "strong duality = closure exact" in the q=+1 converge column.

| pillar | 213 reading | prior entry / object | Lean status |
|---|---|---|---|
| Kantorovich LP cost (primal) | weight-axis cost `Σ d·π` over the coupling-simplex | `measure.md`/`probability.md` weight | **built** (`transportCost`, `rowMarg`/`colMarg`) |
| Monge map (deterministic) | the vertex sub-case of the coupling simplex | weight-axis | conceptual (no `Monge` object) |
| weak duality `dual ≤ primal` | the closure unit `x ≤ star(star x)` | `convex_duality.md` / `FenchelMoreau` | **built** (`kantorovich_weak_duality`) |
| c-transform `f^c` | the c-Fenchel conjugate `(·)^c` (order-reversing) | `convex_duality.md` `(·)*` | closure **built** (`cloAntitone`); cost-pairing object conceptual |
| c-concavity `f=f^{cc}` | the closed/fixed points of the closure | `FenchelMoreau` | **built** (`closed_iff_fixed`) |
| W₁ Kantorovich–Rubinstein `sup_f=inf_π` | the `f**=clo` biconjugation (4th instance) | `FenchelMoreau` | **built** (`biconjugate_eq_clo`, `biconj_idempotent`) |
| strong duality / zero gap (they meet) | closure exact = residue collapse, q=+1 | `galois.md` (fund. thm) | **built** (`ollivier_plan_optimal`, `ollivier_bracket`) |
| duality gap (non-tight) | the closure residue, q=−1 (escape) | `ResidueTag` | **built** as residue concept |
| Brenier `T=∇φ` | `q=+1` gradient of the clo-fixed potential | `convex_duality.md` `GradientFlow` | descent **built**; map/potential object conceptual |

So **YES** — Kantorovich–Rubinstein duality falls out as the `f**=clo` order-reversing closure on the
transport cost (W₁ = `biconjugate_eq_clo`, c-concavity = `closed_iff_fixed`), the Kantorovich LP is the
weight axis with a real ∅-axiom weak-duality + zero-gap theorem, and the gap is the q=±1 residue. OT is
one object read across the weight axis and the closure — **the fourth instance of the order-reversing
closure family, no new axis.**

## Note for the technique — does OT force a new construct?

**Verdict: EXTEND by consolidation — no new primitive.** Every slot OT uses already exists: the
**weight axis** (`measure.md`/`probability.md`, the coupling = a joint weight with marginals); the
**`f**=clo` order-reversing closure** (`FenchelMoreau`/`galois.md`, the c-transform = its cost-pairing
instance); the **adjoint inequality** (`kantorovich_weak_duality` = weak duality); the **q=±1 residue
tag** (`ResidueTag`, the gap). The one sharpening for the closure family: OT shows the closure
`f**=clo` is **read on a weight-axis cost** (a bilinear pairing `Σ d·π`), not just on a function-lattice
— so the family Galois/Legendre/Nullstellensatz/**OT** spans algebra (V⊣I), order (Fix⊣Inv), analysis
(f**), and the **weight axis** (transport), one `biconj_idempotent` across four domains.

## Verified Lean anchors (file:line:theorem — all grep-verified; purity by `tools/scan_axioms.py` from repo root)

| Leg | Theorem (file : name : line) | Status |
|---|---|---|
| **weak duality** `dualValue ≤ transportCost` = the adjoint inequality / `clo` unit (Kantorovich LP) | `Lib/Math/Geometry/DiscreteCurvature/OllivierRicci.lean : kantorovich_weak_duality` (`:52`); defs `transportCost` (`:36`), `dualValue` (`:40`), `rowMarg` (`:30`), `colMarg` (`:33`) | ∅-axiom ✓ (60 pure / 0 dirty) |
| **strong duality / zero gap** (a plan and a potential meet ⟹ optimal) = closure exact | `OllivierRicci.lean : ollivier_plan_optimal` (`:106`), `ollivier_bracket` (`:91`, the gap bracket) | ∅-axiom ✓ (same module) |
| **W₁ = `f**=clo` biconjugation** (Kantorovich–Rubinstein); **c-transform** = conjugate; **c-concavity** = closed/fixed | `Lib/Math/Order/FenchelMoreau.lean : cloAntitone` (`:53`), `biconjugate_eq_clo` (`:59`), `cloAntitone_extensive` (`:72`, weak-dual unit), `star_triple` (`:109`, `f^{ccc}=f^c`), `biconj_idempotent` (`:134`, Fenchel–Moreau), `closed_iff_fixed` (`:152`, **c-concavity / strong dual**), `cloAntitone_eq_gc_clo` (`:187`) | ∅-axiom ✓ (18 pure / 0 dirty) |
| the shared closure machine (Galois/Legendre/Nullstellensatz/OT) | `Lib/Math/Order/GaloisConnection.lean : clo` (`:104`), `clo_extensive` (`:107`), `clo_monotone` (`:114`), `clo_idempotent` (`:126`), `gc_unit` (`:41`), `gc_counit` (`:49`) | ∅-axiom ✓ (15 pure / 0 dirty) |
| the **weight axis** (coupling = joint weight; convolution = independent coupling) | `Lib/Math/Probability/Limit/ConvolveProfile.lean : mass_conv` (`:190`), `momentNum_conv` (`:239`) | ∅-axiom ✓ (20 pure / 0 dirty) |
| the **q=±1 residue tag** (the duality gap: tight q=+1 / gap q=−1) | `Lib/Math/Foundations/ResidueTag.lean : residue_tag_two_poles` (`:228`), `multiplier_unimodular` (`:86`), `golden_is_converge` (`:180`) | ∅-axiom ✓ (55 pure / 0 dirty) |
| measure (σ-algebra-free weight) the coupling is built over | `Lib/Math/Analysis/Measure/DyadicMeasure.lean : measureNum` (`:41`), `measure_union_additive` (`:69`) | ∅-axiom ✓ (referenced, `measure.md`) |
| Brenier `T=∇φ` = the `q=+1` gradient descent fixed point (conceptual weld) | `Lib/Math/Analysis/Optimization/GradientFlow.lean : gradient_descent_monotone`, `gradient_descent_identity` (cited via `convex_duality.md`, 9/0) | ∅-axiom ✓ (descent only; map object conceptual) |

> Axiom-purity note: `OllivierRicci` (60/0), `FenchelMoreau` (18/0), `GaloisConnection` (15/0),
> `ConvolveProfile` (20/0), and `ResidueTag` (55/0) were each re-run through `tools/scan_axioms.py`
> from repo root this session — **168 pure / 0 dirty** across the five modules; `kantorovich_weak_duality`,
> `ollivier_plan_optimal`, `ollivier_bracket`, and every cited `FenchelMoreau`/`ResidueTag` theorem
> individually PURE.

## Conceptual-only legs (honest — NOT grounded in repo Lean; located precisely)

- **The named OT objects `Wasserstein` / `OptimalTransport` / `Monge` / `cTransform` / `Brenier` —
  ABSENT.** Grep over `lean/E213/` (`Wasserstein|OptimalTransport|cTransform|c_transform|cConcav|Monge|
  brenier|kantorovichRubinstein`) returns **zero** named objects — the only hit is the docstring phrase
  "Wasserstein-1 / earth-mover distance" in `OllivierRicci.lean:10`. As predicted, the named layer is
  not built; the *structure* it inhabits (the weight-axis cost, the `f**=clo` closure, the q=±1 gap) is.
- **The `inf_x(c(x,y)−f(x))` c-transform OBJECT** — absent (needs a `Real213`/dyadic function-lattice
  `inf` over the cost pairing). The closure *machine* (`cloAntitone`, both monotone and antitone) is
  certified; only the cost-pairing instance is unwritten — exactly parallel to `convex_duality.md`'s
  missing `sup_x(px−f)` Legendre object and `galois.md`'s missing field-extension instance.
- **A general measure-coupling primitive** — the coupling `rowMarg`/`colMarg`/`transportCost` machinery
  is built **only** as the finite-ℤ `OllivierRicci` instance (`{0,…,n−1}`, signed via `gridSumZ`).
  `DyadicMeasure` gives σ-algebra-free measures, but a coupling of two *general* `DyadicMeasure`s with a
  marginal-projection theorem is not built — the honest measure-coupling gap the brief asked to flag.
  (This is the one genuine "needs a measure-coupling primitive" residual; it is *partially* present — the
  finite case is a real ∅-axiom instance — not wholly absent.)
- **Brenier's map theorem `T=∇φ` and the convex-potential typed object** — absent (no `convexConjugate`,
  no pushforward `T_#μ=ν`). The grounded shadow is the `q=+1` gradient-descent fixed point `∇F=0`
  (`GradientFlow`, via `convex_duality.md`); the c-concave-potential-as-object and the
  `∇φ`-is-the-optimal-map implication are the missing objects, the same gap `convex_duality.md` flags.
- **The W₁ metric axioms / triangle inequality as a typed `Wasserstein` distance** — absent; the
  concrete worked W₁-values exist only as the finite triangle/square/double-star examples in
  `OllivierRicci` (`dualValue = transportCost = 1, 2, 5`), pinned by `ollivier_plan_optimal`.

## Verdict: EXTEND by consolidation (weight axis × `f**=clo`), one PARTIAL — the FOURTH closure instance

Optimal transport **extends and consolidates** — it adds no axis and does not break the model. The
load-bearing legs are grounded ∅-axiom and the corpus already had them: the **Kantorovich LP weak
duality** (`kantorovich_weak_duality`, 60/0), the **zero-gap optimality certificate**
(`ollivier_plan_optimal`), and the **`f**=clo` closure** (`FenchelMoreau`, 18/0) that W₁'s
Kantorovich–Rubinstein duality instantiates. The NEW datum — passing the re-skin guard against
`convex_duality.md` — is that OT's Kantorovich–Rubinstein W₁-duality is the **same `f**=clo` closure
read on the transport cost over measures**, the c-transform = the c-Fenchel conjugate, c-concavity =
`closed_iff_fixed`, making OT the **FOURTH instance of the order-reversing closure family** (Galois /
Legendre–Fenchel / Nullstellensatz / optimal transport), the family now spanning the weight axis. The
one PARTIAL is the **named OT object layer** (`Wasserstein`/`Monge`/`cTransform`/`Brenier`) and a
**general measure-coupling primitive** beyond the finite-ℤ `OllivierRicci` instance — absent, located
precisely: the structure they inhabit is present and certified, only the named instances are unwritten.

> **Open Lean target the calculus names precisely:** define `cTransform (c) (f) (y) := inf_x (c x y −
> f x)` on a `Real213`/dyadic function-lattice, show `(·)^c` is order-reversing, and instantiate
> `FenchelMoreau.cloAntitone` at `star = (·)^c` to obtain `W₁ = f^{cc} = cloAntitone (·)^c` with
> `biconj_idempotent` giving Fenchel–Moreau (`f^{ccc}=f^c`) and `closed_iff_fixed` giving c-concavity —
> the **Kantorovich–Rubinstein duality as the cost-pairing instance of `FenchelMoreau`'s closure**, the
> one weld that would promote this entry's biconjugation leg from abstract-grounded to a closed OT
> derivation (parallel to `ConvolveRescaleContraction` welding the Banach engine to the CLT, and to
> `convex_duality.md`'s named `convexConjugate` weld). A second target: a coupling of two general
> `DyadicMeasure`s with `rowMarg`/`colMarg` projection (lifting `OllivierRicci`'s finite-ℤ coupling to
> the σ-algebra-free measure object) — the measure-coupling primitive.
