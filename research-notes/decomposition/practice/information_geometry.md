# Decomposition: information geometry (KL divergence, Fisher metric, dual-flat ±1 structure)

*213-decomposition per `../README.md` (model v7.1). A **consolidation** target: it folds
`entropy.md` (the `weight∘log-character`, with `−log` *forced* by independence→additivity =
the `×↦+` arrow), `probability.md` (`P = ratio∘count`, the weight-reading), and `curvature.md`
(curvature = the loop-reading's `q=±1` residue, the second-order/Hessian) into one field. The
LEVERAGE hypotheses to DERIVE, not re-skin:*

1. *`D(p‖q)=Σ p·log(p/q)` = `entropy.md`'s `weight∘log-character` applied to a **ratio** `p/q`;
   the **asymmetry** `D(p‖q)≠D(q‖p)` = the log-character evaluated against ONE of the two
   weights = the `q=±1` directionality (`entropy.md`'s directed reading).*
2. *`D≥0` (Gibbs, `=0 ⟺ p=q`) = the divergence is a "distance-like" residue with a fixed point
   on the diagonal `p=q` (the `q=+1` converging pole); positivity = the log-character's
   convexity (Jensen). Does the calculus PREDICT `D≥0` as the convexity residue?*
3. *Fisher metric = the SECOND-ORDER expansion of KL near `p=q` — the **Hessian of the
   divergence** = `curvature.md`'s curvature reading (the second-order residue of the
   loop/diagonal). So Fisher = the curvature of the entropy reading; information geometry =
   `curvature.md` on the space of weights.*
4. *Bregman / dual-flat (±1) connections = the `q=±1` pair of the convex potential (the
   e-connection / m-connection = the two directions of the character arrow).*

> **Note on repo coverage — the honest split up front.** Of the four objects, **only KL is
> built**, and only in the *atomic dyadic* clamp form `klBitsDyadic a b = a − b`
> (`KLDivergence.lean`). The **divergence functional** `Σ p·log(p/q)` (a sum over a
> distribution of log-ratios), the **Fisher metric** (a Hessian on weight-space), the **Bregman
> divergence**, and the **dual-flat (e/m) connections** are *absent* — grep on `lean/E213` for
> `fisher`/`bregman`/`relativeEntropy`/`metric` (in this sense) returns **nothing**. So this is a
> **PARTIAL** entry like `knots.md`/`representation.md`: the consolidating *picture* is right and
> three of its load-bearing pieces are each a Lean theorem from a sister decomposition, but the
> two *specifically-geometric* legs (a divergence functional + its Hessian) are the located
> missing leg. The verdict states this precisely.

## The decomposition (C / Reading / Residue)

- **Construction `C`** — the same distinguishing as `entropy.md`/`probability.md`: a **family of
  distinguishables** read through the **weight-reading** to a `ProbabilityCut` (`num/den`,
  `0<den`, `num≤den`). Information geometry adds **no new construction** — its "manifold of
  distributions" is just the *space of weight-readings* on the one `C` (each point = one
  `ProbabilityCut`). The dyadic substrate: a point is `p = 1/2^a`, the manifold-coordinate is the
  surprise depth `a` (`Bit.lean`, `dyadicProbabilityCut`).

- **Reading `L`** — a **TWO-WEIGHT comparison** of `entropy.md`'s `weight∘log-character`. Where
  `entropy.md` reads ONE weight `p` through the log-character and takes its expectation
  (`H = E[−log p]`), information geometry reads the log-character of a **ratio of two weights**
  `p/q` and takes the expectation **against `p`**:
  `D(p‖q) = Σ_x p(x)·log(p(x)/q(x)) = E_p[ log p − log q ]`.
  - The `log(p/q) = log p − log q` step is the SAME `×↦+` character of `entropy.md`/`vp_mul`
    (a *ratio* becomes a *difference of depths*). On the dyadic substrate this is exactly
    `klBitsDyadic a b = a − b` — the surprise-depth difference (`KLDivergence.lean:26`).
  - The expectation `E_p[·]` is `probability.md`'s `discreteNum` weight-reading
    (`Expectation.lean:62`, `discreteNum_append` = linearity).
  So **`D = weight_p ∘ (difference-of-log-characters)`** — `entropy.md`'s composite, with the
  character's operand a *ratio* and the weight slot fixed to *one* of the two arguments.

- **Residue** — `q = ±1`, the SAME tag as `curvature.md`/`entropy.md`, here read TWICE:
  - **directionality (1st-order):** the weight is taken against `p`, not `q` — the
    `entropy.md` "directed reading" with a fixed `q=±1` orientation bit. This is the source of
    the **asymmetry** `D(p‖q)≠D(q‖p)`.
  - **the diagonal `p=q` (2nd-order):** `D` has a fixed point on `{p=q}` where the two
    weight-readings coincide (`D=0`); near it `D` is *convex with vanishing gradient*, and the
    **Fisher metric = its Hessian** would be the `q=+1` converging residue of the loop/diagonal
    reading — `curvature.md`'s second-order residue, transplanted to weight-space. THIS residue
    (the Hessian) is the **missing leg** (no second-order divergence object in Lean).

## Re-seeing — ⟨C | L⟩

```
   point of the manifold   =  ⟨ family of distinguishables | weight-reading ⟩ = ProbabilityCut   (probability.md C)
   surprise −log p         =  ⟨ p = 1/2^a | log-character ⟩ = depth a                              (surprise_dyadic_eq_depth, rfl)
   log(p/q) = log p − log q=  the ×↦+ character eating a RATIO = depth difference a − b            (= klBitsDyadic a b, KLDivergence.lean:26)
   D(p‖q)                  =  ⟨ (p, q) | weight_p ∘ (log-character of the ratio) ⟩ = E_p[log p−log q]
   D(p‖q) on dyadic atoms  =  a − b  (clamped)                                                     (klBitsDyadic, kl_fair_to_quarter:1)
   ASYMMETRY D(p‖q)≠D(q‖p) =  the clamp: a−b vs b−a, only one survives  (q=±1 direction bit)        (klBitsDyadic 2 1 = 1 ; klBitsDyadic 1 2 = 0)
   D≥0 (Gibbs)             =  Nat-sub is ≥ 0                                                        (kl_nonneg = Nat.zero_le)
   D=0 ⟺ p=q (fixed point) =  a − a = 0  (the diagonal, q=+1 converging pole)                       (kl_self_zero = Nat.sub_self)
   Fisher metric           =  Hessian of D at p=q  =  curvature.md's 2nd-order loop-residue          ✗ NOT BUILT (missing leg)
   e- / m-connection (±1)  =  the two directions of the character arrow (Bregman ±)                  ✗ NOT BUILT (conceptual)
```

**(1) KL = the entropy log-character's asymmetry residue — CONFIRMED on the dyadic atom.** The
hypothesis lands exactly. `D(p‖q)` is `entropy.md`'s reading with the character's operand changed
from a single weight `p` to the *ratio* `p/q`; the `×↦+` arrow turns that ratio into a
**difference of surprise depths** `a − b`, which is *literally* the repo's `klBitsDyadic a b = a − b`
(`KLDivergence.lean:26`, PURE). So KL is not a new object — it is the entropy composite
`weight∘character` read on a two-weight ratio. The **asymmetry is the `q=±1` direction bit made
concrete by the clamp**: `klBitsDyadic 2 1 = 1` (`kl_fair_to_quarter`, `rfl`) but `klBitsDyadic 1 2
= 0` (`Nat`-sub clamps the reverse to zero) — `D(p‖q) ≠ D(q‖p)` because the surprise-depth
*difference* is **directed**, exactly `entropy.md`'s directed (one-sided) reading. This is the
first hypothesis, certified at the atom.

**(2) D≥0 (Gibbs) = the `q=+1` fixed point on the diagonal — CONFIRMED at the atom, but the
convexity content is a stand-in.** `D≥0` is `kl_nonneg : 0 ≤ klBitsDyadic a b`, which is just
`Nat.zero_le` (`KLDivergence.lean:33`, PURE), and `D=0 ⟺ p=q` is `kl_self_zero : klBitsDyadic a a
= 0 = Nat.sub_self` (`:29`). So the divergence *does* have a fixed point on the diagonal `{a=b}` —
the `q=+1` converging pole, the place where the two weight-readings coincide, identified by
`ResidueTag`'s `converge_residue_fixed` (`ResidueTag.lean:160`, PURE). **But the honest strain:**
in the dyadic atomic form, `D≥0` is *Nat-subtraction monotonicity*, NOT Jensen's convexity
inequality. The repo says so verbatim (`KLDivergence.lean:16-17`: "Jensen's inequality in dyadic
Lens coordinates becomes the monotonicity of `Nat`-subtraction; `D(p‖q)≥0` is just `Nat.zero_le`").
The calculus *predicts* `D≥0` as the diagonal fixed-point/`q=+1` residue (and the atom certifies it
that way), but the **general convexity-of-`−log` ⟹ Jensen ⟹ Gibbs** chain — the sum over a full
distribution of log-ratios — is **not** a Lean theorem (no convex-functional object;
`grep convex` in `lean/E213` hits only HeatEq energy decay, not information geometry). So leg (2) is
PREDICTED + atom-certified, general-convexity OPEN.

**(3) Fisher = the Hessian of KL near `p=q` = `curvature.md` on weight-space — PREDICTED, NOT
BUILT.** This is the consolidation's sharpest claim and its located break. The picture is exact:
expand `D(p‖p+dp)` to second order; the first-order term vanishes (the diagonal is the `q=+1`
fixed point, leg 2), so the **leading term is the Hessian**, and *that* quadratic form is the
Fisher information metric. This is *structurally identical* to `curvature.md`: curvature is the
**second-order residue of the loop-reading** at the flat/`det=1` point (the `q=+1` pole), born when
the first-order (flat) reading's residue first becomes nonzero. Fisher is the same shape — the
second-order residue of the *divergence* reading at the diagonal. The two are one object read on two
`C`'s: `curvature.md` on `List Mat2` paths, Fisher on the space of weights. **But the Hessian
machinery does not exist here.** The repo has a *first*-derivative `IsDifferentiable`/`.derivative`
on `Real213` cut-functions (`ODE.lean:124`) and even a `linearWithIntercept_secondDerivable` (a
second-derivative *witness*, `ODE.lean:124-128`, giving `d²/dx²[ax+b]=0`), but there is **no Hessian
of a divergence functional**, no metric tensor on `ProbabilityCut`-space, no `fisher`/`metric`
object anywhere (grep: nothing). So leg (3) is the **precise missing leg**: a divergence
*functional* `Σ p·log(p/q)` (over a distribution, not two atoms) AND its **second-order expansion
(Hessian) at the diagonal**. The calculus predicts Fisher = `curvature.md`'s residue on weight-space;
the repo proves neither the functional nor its Hessian.

**(4) Bregman / dual-flat (e/m, ±1) connections = the two directions of the character arrow —
CONCEPTUAL.** The hypothesis maps cleanly onto the established structure but is wholly un-built. A
Bregman divergence `D_φ(p,q) = φ(p) − φ(q) − ⟨∇φ(q), p−q⟩` is the convex-potential generalization of
KL (with `φ = Σ p log p`, the negative entropy); the **e-connection (exponential family) and
m-connection (mixture family) are the dual `±1` pair** — exactly `curvature.md`/`exponential.md`'s
*bidirectional* character arrow (`×↦+` one way, `+↦×` the other) read as the two flat connections on
weight-space, with the Fisher metric the `q=+1` symmetric part between them. This is the most
appealing consolidation (dual-flatness = the `q=±1` residue tag, `ResidueTag.residue_tag_two_poles`,
PURE) — but there is **no convex potential, no connection, no Bregman object** in `lean/E213`. It is
recorded as the prediction the structure *forces* once leg (3)'s functional+Hessian is built; it is
*conceptual-only* today.

## Revelation — info geometry = the entropy character read as a two-weight ratio, whose Hessian on the diagonal is curvature

**Collapse + forcing (the picture is one object; the geometric legs are the located break).**
Information geometry consolidates the three sister decompositions into a single statement, and the
consolidation is *forced*, not decorative:

- **KL = `entropy.md`'s `weight∘log-character`, with the character eating a RATIO `p/q`.** The
  `×↦+` arrow turns the ratio into a **difference of surprise depths** `a−b` — literally
  `klBitsDyadic a b = a−b` (PURE). The **asymmetry `D(p‖q)≠D(q‖p)` is the `q=±1` direction bit**
  realized by the clamp (`a−b` survives, `b−a→0`): the surprise-depth difference is *directed*, the
  one-sided (against-`p`) reading. **Hypothesis 1: CONFIRMED at the atom.**
- **`D≥0`, `=0⟺p=q` = the `q=+1` converging fixed point on the diagonal.** `kl_nonneg`
  (`Nat.zero_le`) and `kl_self_zero` (`Nat.sub_self`) certify the diagonal fixed point exactly as
  `ResidueTag.converge_residue_fixed` — but the *convexity/Jensen* content collapses to `Nat`-sub
  monotonicity on the atom and is **not** proved as Jensen on a general distribution.
  **Hypothesis 2: PREDICTED + atom-certified, general convexity OPEN.**
- **Fisher = the Hessian of KL at the diagonal = `curvature.md`'s second-order residue, on
  weight-space.** Same shape as curvature (the second-order residue of a reading at its `q=+1`
  flat/fixed point), one `C` swapped (paths → weights). **This is the located break: there is no
  divergence functional and no Hessian object in `lean/E213`.** **Hypothesis 3: PREDICTED, NOT
  BUILT — the precise missing leg.**
- **Bregman / dual-flat (e/m) = the bidirectional character arrow's `±1` pair, Fisher the symmetric
  `q=+1` part.** Forced by the structure once (3) exists; **conceptual-only today.**
  **Hypothesis 4: CONCEPTUAL.**

**The deepest unity surfaced.** The single `×↦+` character now runs through information geometry too,
and it does so *twice*: once as the **ratio→difference** (KL, first order) and once as the would-be
**Hessian→Fisher** (second order). Stacked against `curvature.md`'s capstone — the one `det`/`×↦·`
character read *scalar/Aut-invariant/around-a-loop/down-the-height* — information geometry is the
**`×↦+` character read at two orders on weight-space**: first order = KL (the directed `q=±1`
difference), second order = Fisher (the `q=+1` diagonal residue = curvature). `entropy.md` = the
0th/expectation order; KL = the 1st/difference order; Fisher = the 2nd/Hessian order. **Entropy,
relative entropy, and the Fisher metric are one character read at three orders** — that is the
consolidation, and it is the genuine (if partly-predicted) Revelation.

**The honest boundary (PARTIAL, like `knots.md`).** What is *built and PURE*: KL as the directed
surprise-depth difference with its `q=±1` asymmetry and `q=+1` diagonal fixed point (`klBitsDyadic`,
`kl_nonneg`, `kl_self_zero`); all the entropy/expectation/character anchors it rides on. What is
*predicted but un-built* — **the precise missing leg**: (i) a **divergence functional**
`D(p‖q)=Σ_x p(x)·log(p(x)/q(x))` over a full distribution (the repo has only the two-atom dyadic
clamp `a−b`, not the sum-over-outcomes); (ii) its **second-order expansion / Hessian at the
diagonal** = the **Fisher metric** (no metric object, no Hessian-of-functional; only a first-order
`IsDifferentiable` and a trivial `secondDerivable` witness exist); and downstream (iii) Bregman /
the dual-flat e/m connections (conceptual). Legs (i)+(ii) are the same intersection `entropy.md`
already named open — `weight × character` at **non-power resolution** (where `−log p` leaves `Nat`
and lands in the `Real213` `log₂e` bracket residue, `chebyshev_constant_interval`) — now extended
*one order up* (the Hessian). Information geometry's continuous content lives exactly at the residue
`entropy.md` flagged, plus its second derivative.

## Note for the technique — does info geometry CONSOLIDATE entropy + probability + curvature?

**YES as a picture, decisively; PARTIAL as Lean.** Three lessons:

1. **The `×↦+` character is read at *orders*, not just at *places*.** `curvature.md` found one
   character read across {scalar, Aut, loop, height} — different *places*. Information geometry adds
   a new axis of reuse: the *same* `×↦+` arrow read at **order 0 (entropy/expectation), order 1
   (KL/directed difference), order 2 (Fisher/Hessian)**. The README's "character-mode" parameter
   gains an *order* reading — and order-2 IS `curvature.md`'s second-order residue, so the
   consolidation entropy+curvature is *the same character at two orders on weight-space*. No new
   primitive; a new way the existing invariants stack.

2. **The `q=±1` residue tag does double duty here.** KL's **asymmetry** is the `q=±1` *direction*
   bit (the clamp picks one orientation); KL's **non-negativity/fixed-point** is the `q=+1`
   *converge* pole (the diagonal). And the dual-flat e/m connections are the `±1` *pair* of the
   character arrow. So one `ResidueTag` carries all three of info geometry's "miracles"
   (asymmetry, positivity, duality) — the cleanest single-tag reuse since `measure.md`.

3. **The located break is precise and one notch up from `entropy.md`'s.** `entropy.md` named the
   open leg as the *general real-valued `−Σ p log p`* (the functional, order 0/1). Information
   geometry names it *one order higher*: the divergence **functional** AND its **Hessian** (Fisher),
   plus the connections (Bregman). This is a clean *promotion target*, not a failure — build the
   `Σ p·log(p/q)` functional on `ProbabilityCut`-lists (the natural next file after
   `KLDivergence.lean`), then its second-order expansion at the diagonal, and Fisher = the
   `curvature.md` residue lands as a theorem. The calculus *predicts* the whole tower; the repo has
   the atom (KL) and the picture.

**Verdict: information geometry CONSOLIDATES entropy + probability + curvature (PARTIAL — atom
built, functional+Hessian missing).** KL **falls out** as the entropy log-character's directed
asymmetry residue with a `q=+1` fixed point at `p=q` — *confirmed at the dyadic atom* (`klBitsDyadic
= a−b`, `kl_nonneg`, `kl_self_zero`, all PURE), the asymmetry being the clamp's `q=±1` direction
bit. `D≥0` is predicted as the diagonal/`q=+1` residue and atom-certified (as `Nat`-sub, not yet as
Jensen-convexity). **Fisher = the Hessian of KL = `curvature.md`'s second-order residue on
weight-space is PREDICTED but NOT BUILT** — the precise missing leg is *a divergence functional
`Σ p·log(p/q)` + its Hessian at the diagonal* (with Bregman/e-m connections downstream-conceptual).
The model v7.1 holds (no break to the interior; this is a located PARTIAL, the geometric legs absent
exactly where `entropy.md`'s residue lives, one order up). One arrow (`×↦+`), now read at three
orders.

---

### Verified Lean anchors (all ∅-axiom; checked by `tools/scan_axioms.py` + grep on `lean/E213`)

| Leg | Theorem (file:line : name) | Status |
|---|---|---|
| ★ KL = directed surprise-depth difference (ratio→difference) | `Probability/Information/KLDivergence.lean:26 : klBitsDyadic` (`a − b`) | PURE ✓ |
| ★ asymmetry `D(p‖q)≠D(q‖p)` = the `q=±1` clamp/direction bit | `…/KLDivergence.lean:37 : kl_fair_to_quarter` (`klBitsDyadic 2 1 = 1`); reverse `klBitsDyadic 1 2 = 0` by `Nat`-sub clamp; `:39 kl_byte_to_bit` | PURE ✓ |
| ★ `D≥0` (Gibbs) = `q=+1` / Nat-sub monotonicity | `…/KLDivergence.lean:33 : kl_nonneg` (`= Nat.zero_le`) | PURE ✓ |
| ★ `D=0 ⟺ p=q` = the diagonal fixed point (`q=+1` converge pole) | `…/KLDivergence.lean:29 : kl_self_zero` (`= Nat.sub_self`); `:43 kl_collapse_when_equal` | PURE ✓ |
| log-character: `−log p` = surprise depth (ratio's two halves) | `Probability/Information/Entropy.lean:55 : surprise_dyadic_eq_depth`; `:52 surpriseBitsDyadic` | PURE ✓ |
| `log(p/q)=log p−log q` = `×↦+` on a ratio | `…/Entropy.lean:90 : surprise_additive` (`rfl`) | PURE ✓ |
| entropy = expectation of the character (order 0) | `…/Entropy.lean:83 : entropy_additive`; `:35 shannonEntropy_uniform_eq_depth` | PURE ✓ |
| weight-reading / expectation `E_p[·]` (the `Σ p·(·)` slot) | `Probability/Foundation/Expectation.lean:62 : discreteNum_append` (linearity); `discreteNum`, `expectation_master` | PURE ✓ |
| independence = ×-product of weights (the ratio's denominators) | `Probability/Information/MutualInfo.lean:32 : joint_independent_eq_sum`; `Probability/Foundation/Independence.lean : joint`, `joint_assoc_num` | PURE ✓ |
| × character (cross-domain `×↦+` anchor) | `Meta/Nat/VpMul.lean:165 : vp_mul`, `vp_pow` | PURE ✓ |
| `q=±1` residue tag (asymmetry/positivity/duality carrier) | `Lib/Math/Foundations/ResidueTag.lean:228 : residue_tag_two_poles`; `:160 converge_residue_fixed`; `:133 escape_residue_outside`; `multiplier_unimodular` | PURE ✓ |
| residue at non-dyadic resolution (where Fisher's continuous content lives) | `Lens/Number/Nat213/ChebyshevLower.lean:387 : chebyshev_constant_interval` (`log₂e ∈ [(m+1)/(2(m+2)), 6]`) | PURE ✓ (prior, `entropy.md`) |
| curvature = 2nd-order loop-residue (the shape Fisher would instantiate) | `…/HolonomyLattice.lean : det_holonomy_eq_one`, `first_loop_is_the_fold`; `DiscreteGaussBonnet.lean : gauss_bonnet_Kmn` | PURE ✓ (prior, `curvature.md`) |

(KLDivergence + Entropy scanned together: **20 PURE / 0 dirty**. ResidueTag key theorems: PURE.)

### Conceptual-only / ABSENT legs (honest — the located break)

- **The divergence FUNCTIONAL `D(p‖q)=Σ_x p(x)·log(p(x)/q(x))`** — a sum over a *distribution* of
  log-ratios — is **ABSENT** in `lean/E213`. The repo builds only the two-atom dyadic clamp
  `klBitsDyadic a b = a − b` (`KLDivergence.lean`); there is no `relativeEntropy`/`KullbackLeibler`
  functional over a `ProbabilityCut`-list. **This is missing-leg part (i).**
- **The FISHER information metric** — the **Hessian of `D` at the diagonal `p=q`** — is **ABSENT**:
  grep `fisher`/`metric`(in this sense)/`hessian` over `lean/E213` returns nothing for information
  geometry. The repo has a first-order `IsDifferentiable`/`.derivative` on `Real213` cut-functions
  (`Analysis/ODE/ODE.lean:124`) and a trivial `linearWithIntercept_secondDerivable` witness, but
  **no Hessian of a divergence functional and no metric tensor on weight-space**. **This is
  missing-leg part (ii)** — `curvature.md`'s second-order residue on a `C` (weights) the repo does
  not yet equip with a connection.
- **Bregman divergence + the dual-flat (e/m, `±1`) connections** — **ABSENT**: no convex potential
  `φ = Σ p log p`, no connection object, no Bregman functional. Predicted as the `q=±1` pair of the
  character arrow (with Fisher the symmetric `q=+1` part) once (i)+(ii) exist; **conceptual-only.**
- **General convexity / Jensen ⟹ Gibbs** for a full distribution is **not** a theorem: on the atom
  `D≥0` is `Nat.zero_le` (`Nat`-sub monotonicity), the repo's own note (`KLDivergence.lean:16-17`).
  The convexity-of-`−log` proof would ride the same `Real213` `log₂e` residue as `entropy.md`'s open
  general entropy — i.e. the missing functional + its second derivative live at the
  `weight × character`-at-non-power-resolution intersection, one order up.
