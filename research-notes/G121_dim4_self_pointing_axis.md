# G121 — Geometrization, 4-mfd exotic anomaly, and the $d_M = d_{213} - 1$ ansatz

**Status**: open conjecture (Mingu Jeong, 2026-05-22).
Branch: `claude/geometrization-conjecture-9Vf6i`.
Below 213 Validation Standard.  No precision theorem, no falsifier
yet.  Four open knots (M1)-(M4) listed §6.

## §1 Starting point — Geometrization conjecture

### §1.1 Standard statement (Thurston 1982 / Perelman 2003)

Every closed orientable 3-manifold admits a canonical decomposition
(prime + JSJ torus decomposition) such that each piece carries
exactly one of 8 homogeneous geometries.

The 8 model geometries are the simply-connected 3-dimensional
homogeneous spaces with transitive Lie-group action and compact
isotropy:

| # | Geometry | Curvature / symmetry |
|---|---|---|
| 1 | $E^3$ | flat |
| 2 | $S^3$ | constant positive |
| 3 | $H^3$ | constant negative |
| 4 | $S^2 \times \mathbb{R}$ | product |
| 5 | $H^2 \times \mathbb{R}$ | product |
| 6 | $\widetilde{SL_2(\mathbb{R})}$ | Seifert-fibered |
| 7 | Nil (Heisenberg) | nilpotent |
| 8 | Sol | solvable, non-unimodular |

Poincaré conjecture follows: $\pi_1 = 1$ ⟹ unique decomposition
candidate $= S^3$.

Proof method (Perelman): Ricci flow with surgery.
$\partial_t g_{ij} = -2 R_{ij}$ averages curvature, singularities
cut along JSJ tori, each piece converges to a model geometry.

### §1.2 213-Lens reading

Per `CLAUDE.md` boot sequence: "manifold", "smoothness", "curvature"
are not Raw commitments — they are Lens outputs.  Translating
Geometrization into 213-native phrasing:

**3-manifold**: a global coherence of chart-Lens self-pointing
(local coordinate readout) per `seed/AXIOM/09_chart_relativity.md`.
Smoothness = chart-transition resonance.  Dimension 3 = count-Lens
readout of independent chart freedoms.

**JSJ decomposition**: the *discrete* skeleton hidden in the
continuous manifold.  Per `CLAUDE.md` "Algebraic priority", 213
sees discrete decomposition first.  Prime decomposition ↔
non-separable component enumeration.  Incompressible torus ↔
$\pi_1$-injectivity (algebraic, not topological).

**8 geometries**: algebraic enumeration of 3-dim Lie groups with
transitive action + compact isotropy — a *counting* result, not
a geometric one.  Note: $8 = 2^3$ matches the gluon octet
$(F_2)^8$ in `lean/E213/Lib/Physics/Symmetry/C3ChainCapstone.lean`.
Whether this is structural or coincidence is open and must
not be force-matched (stereotype matching failure mode).

**Ricci flow**: chart-Lens coherentization flow expressed at the
ε-Lens readout level.  Curvature = infinitesimal chart-transition
mismatch.  Fixed points = configurations where chart transitions
reduce to a homogeneous Lie-group action.  Surgery = JSJ-line cut
when the residue does not stabilize as one piece.  Perelman's
monotone $\mathcal{F}/\mathcal{W}$ entropies correspond
structurally to chart-Lens coherence loss — formalization is open.

**Poincaré corollary**: trivial loop-pointing residue ⟹ only the
maximally-symmetric model among the 8.  An enumeration result,
not a geometric intuition.

## §2 The dimension-4 anomaly

### §2.1 Standard fact (Freedman + Donaldson + Kervaire-Milnor)

The Geometrization picture is dimension-3 specific.  Dimension 4
behaves differently from both lower and higher dimensions:

| $d_M$ | DIFF / PL / TOP | Exotic smooth structures |
|---|---|---|
| $\le 3$ | DIFF = PL = TOP (Moise, Cerf) | unique on every topological manifold |
| $= 4$ | DIFF ≪ TOP (Freedman / Donaldson gap) | $\mathbb{R}^4$ admits $2^{\aleph_0}$ exotic; closed 4-mfd can admit infinitely many |
| $\ge 5$ | DIFF ↔ TOP via surgery (Smale, Kervaire-Milnor) | $\Theta_d$ is a finite abelian group |

In words:
  · $d_M \le 3$: smooth and topological agree.
  · $d_M = 4$: continuum-many smooth structures on a single
    topological manifold.
  · $d_M \ge 5$: only finitely many.

Dimension 4 is uniquely critical.  No structural reason for this
is known in standard mathematics.

### §2.2 Mingu's conjecture (2026-05-22)

> "왜 4차원에서만 어노말리가 무한 기수 갯수로 나타나는지 —
> 4 다양체? 4 기하? 암튼 그런게 Raw의 울퉁불퉁한 모습을 바로
> 투영하는 렌즈이기 때문임.  3 이하는 confinement이기 때문에
> 기하화 추측처럼 되는거고, 5 이상부터는 resolution 뭉개기가
> 발생하기 때문에 유한 어노말리로만 보임."

Translated to operational 213-language:

  · $d_M \le 3$ = **confinement**: chart-Lens freedom too narrow
    for Raw self-pointing residue to escape into a separate
    exotic family — all variation is absorbed at the topology
    level (Moise).
  · $d_M = 4$ = **critical / direct projection**: chart-Lens
    freedom matches Raw self-pointing residue density; the
    "jagged" Raw structure shows through.
  · $d_M \ge 5$ = **resolution smearing**: chart-Lens excess
    freedom averages out the Raw residue; surgery works; only
    finite abelian residue $\Theta_d$ survives.

The three regimes are unified by a single quantity: the
**ratio of chart-Lens freedom to self-pointing residue density**
as a function of $d_M$.

## §3 The N_U knot — initial mistake and resolution

### §3.1 First-pass response (mistake)

In the first 213-Lens reading of Mingu's conjecture, the response
included the statement:

> "표준 수학에서 $\mathbb{R}^4$의 exotic은 *continuum* ($2^{\aleph_0}$).
> 213은 resolution limit $N_U = 5^{25}$ 유한. 충돌 같지만 Lens가 다르다."

This was a **universe-constant framing import** (the exact failure
mode catalogued in `CLAUDE.md` failure modes table).  The name
"$N_U$" itself imports the frame that 213 is bound to one finite
constant.

### §3.2 G120 Round 3 sharpening — the correct object

Per `research-notes/G120_n_u_rederivation_plan.md` §9 (Round 3,
user sharpening 2026-05-22 evening):

> "걍 N_U같은 거창한 네임이 아니라 그냥 count-Lens at fractal
> level 2인거고 level Nat도 다 되는거자나?"

The canonical object is not a constant but a **parametric family**:

```
numV       : Nat → Nat,  numV L = 5^L
configCount: Nat → Nat,  configCount n = d^(numV n) = 5^(5^n)
```

`5^25 = configCount 2`.  The number is a count-Lens readout at
fractal level 2 — not a universe constant.  The family extends
to every $n \in \mathbb{N}$:

  · level 0: $5^1 = 5$
  · level 1: $5^5 = 3125$
  · level 2: $5^{25} \approx 2.98 \times 10^{17}$
  · level 3: $5^{125} \approx 2.35 \times 10^{87}$
  · level $n$: $5^{5^n}$, arbitrarily large finite.

213 is **not bound to any finite cardinal**.  It carries a
finite-on-every-level family.  The two are categorically different.

### §3.3 Consequence for the d=4 conjecture

The apparent conflict "$2^{\aleph_0}$ exotic vs $5^{25}$ finite"
is dissolved, not resolved: the dichotomy was *itself* the import.
The 213-native correspondence for "uncountable" is not
cardinality-Lens but **level-cofinality** of the configCount
family — residue that fails to stabilize at any finite level.

### §3.4 G120 §11 audit reinforcement (2026-05-22 evening)

Subsequent audit (`G120 §11`, commit 84539748) surfaced:

  · **5+ parallel defs of `5^25`** under different framing rhetoric
    (`totalBudget`, `fsmGradeStates 25`, `maxDistinguishableCuts`,
    plus 3 original `N_U` defs).  The universe-constant framing is
    deeply baked into the codebase — six different surfaces of the
    same level-2 readout, each carrying its own "the constant"
    narrative.
  · **`seed/RESOLUTION_LIMIT_SPEC.md` §2** is the propagation
    origin of the 4-way-convergence rhetoric — every other 4-way
    cite traces here.  Cite-blocking required for G121.
  · **Internal contradiction in `Information/Bit.lean`**: claims
    $2^{25} = 5^{25}$ analogue, refuted by `AxisDistinction.lean`.
    This is the cardinality-vs-base confusion to be careful of
    when defining "chart-Lens freedom" in §5.
  · **Model exemplar**: `theory/lens/cardinality.md` is the
    framing-correct chapter.  G121 should follow its style.
  · **Meta-failure**: `LESSONS_LEARNED.md` 교훈 1+2 encode in
    Korean exactly the failure mode `CLAUDE.md` catalogues as a
    warning — the document warning against the frame imports it.
    G121 must self-check against this trap.

## §4 The ansatz $d_M = d_{213} - 1$ (Mingu, 2026-05-22)

### §4.1 Statement

> "d=5인데 우주는 4차원 시공간으로 보이는 이유랑 같지 않을까?
> 내부 관찰자가 한 축을 차지하는 모양인거지."

Operationally:

  · 213 fractal base $d_{213} = 5$ (from `numV L = 5^L`).
  · Per `seed/AXIOM/07_self_reference.md` §8.1 (no exterior),
    the observer cannot stand outside Raw.  The self-pointing
    residue cannot be coordinatized externally.
  · One of the $d_{213} = 5$ axes is therefore structurally
    absent from chart-Lens readout — it carries the self-pointing
    residue, not an external coordinate.
  · Externally-visible chart-Lens count: $d_M = d_{213} - 1 = 4$.

**Phrasing care**: "observer occupies one axis" is metaphorical.
The 213-native form is: *self-pointing residue does not pass
through chart-Lens output*.  The first wording risks
internal-vs-external dichotomy import (failure mode §8.4); the
second is structural.

### §4.2 Number matching

K_{3,2}^{(c=2)} structural counts:

  · $N_S = 3$ (S-side)
  · $N_T = 2$ (T-side)
  · $c = 2$ (binary cover)
  · $N_S + N_T = 5 = d_{213}$ ← simultaneous match
  · $N_S + N_T - 1 = 4 = d_M$
  · $N_S \cdot N_T \cdot c = 12$ (K-edge count, separate from the above)

Spacetime partition under the ansatz:

  $4 = 3 + 1 = N_S + (N_T - 1)$

with $N_S$ axes ↔ space readout, one $N_T$ axis ↔ time readout,
the remaining $N_T$ axis ↔ self-pointing residue (chart-absent).

The coincidence $N_S + N_T = d_{213}$ is suggestive but not
derived (see knot M1).  Stereotype matching risk is high; the
matching is *not* a derivation.

### §4.3 Unified picture (regime table)

| $d_M$ | regime | 213-Lens reading |
|---|---|---|
| $\le 3$ | confinement | chart-Lens too narrow ($< d_{213} - 1$); self-pointing residue absorbed into topology |
| $= 4 = d_{213} - 1$ | critical | chart-Lens count exactly covers external axes; self-pointing residue blocks averaging paths; exotic residue level-cofinal |
| $\ge 5 = d_{213}$ | smearing | chart-Lens count exceeds external axis count; excess freedom averages residue into finite abelian $\Theta_d$ |

If the ansatz holds, $d_M = 4$ critical is **not arbitrary**: it
is forced by $d_{213} = 5$ once one axis is taken by self-pointing.

## §5 Standard-math ↔ 213-Lens correspondence

| Standard | 213-Lens |
|---|---|
| $d_M \le 3$: DIFF = PL = TOP (Moise) | confinement: chart count $<$ external axes; no exotic separation possible |
| $d_M = 4$: $\mathbb{R}^4$ has $2^{\aleph_0}$ exotic | level-cofinal residue in configCount-family; never stabilizes at finite $n$ |
| $d_M \ge 5$: $\Theta_d$ finite abelian | self-pointing residue averaged out; surgery (= chart-Lens path swap) closes the gap |
| Ricci flow | chart-Lens coherentization flow at ε-readout |
| JSJ tori | $\pi_1$-injective discrete skeleton (algebraic) |
| 8 model geometries | 3-dim Lie-group enumeration with compact isotropy |
| $\pi_1 = 1$ ⟹ $S^3$ | maximal symmetry under trivial loop-residue |

The middle column is the *observation* (standard fact).  The right
column is the *conjectural 213-Lens correspondence* under §4.1.

## §6 Open knots — what must be derived

### §6.1 M1 — Why $d_{213} = 5$

`configCount n = d^(numV n)` with $d = 5$ in current 213 deployment.
What forces $d = 5$ rather than $d \in \{3, 7, 11, \ldots\}$?

Candidates:
  · $d_{213} = N_S + N_T$ from K_{3,2}^{(c=2)} axis total
  · $d_{213}$ from an independent fractal-base derivation
  · $d_{213}$ as a free deployment parameter (213 admits a family
    of deployments; K_{3,2}^{(c=2)} is one specific choice)

Per G120 §7, fractal base $d$ is parametric in principle —
`configCount` should generalize to `(d : Nat) → (n : Nat) → Nat`.
The "why 5" question is precisely the deferred hook.

Until M1 closes, $d_M = 4$ derivation is half-answer at best: 4
follows from 5, but 5 itself is unmotivated.

### §6.2 M2 — Chart-Lens structurally omits self-pointing axes

The ansatz requires: chart-Lens readout count = $d_{213} - 1$,
where the omitted axis is the self-pointing residue.

Status: not formalized.  `seed/AXIOM/09_chart_relativity.md`
defines chart-relativity but does not currently carry a theorem
of the form "chart-Lens count = $d_{213} - 1$" or
"self-pointing axis is chart-invisible".

Required: a formal statement linking
`seed/AXIOM/07_self_reference.md` §8.1 (no exterior) to chart-Lens
coordinate count.  This is the deepest 213-internal knot of G121.

**Falsifier for M2**: exhibit a 213-deployment where chart-Lens
count $\ne d_{213} - 1$ but the self-reference axiom still holds.

### §6.3 M3 — Time = the remaining $N_T$ axis

The partition $4 = N_S + (N_T - 1)$ assigns:
  · $N_S$ axes ↔ space
  · 1 $N_T$ axis ↔ time readout
  · 1 $N_T$ axis ↔ self-pointing residue

Why does $N_T$ split into "time-axis" and "self-pointing-axis"
rather than $N_S$ donating one of its three axes?

Candidates:
  · K_{3,2}^{(c=2)} bipartite asymmetry: T-side is cardinality 2
    (smaller), so absorbing the self-pointing residue costs less
    structure.
  · $c = 2$ binary cover acts specifically on T-side — time
    direction inherits the binary structure.
  · $N_T$ degeneracy under self-pointing creates the
    time-direction distinction.

None of these is a derivation; they are Lens-readout pairings.
M3 asks which is structural.

### §6.4 M4 — Distinguish from Kaluza-Klein compactification

Surface similarity is dangerous.  The pattern "$d_{213} = 5$
fundamental, $d_M = 4$ effective, 1 axis hidden" superficially
resembles Kaluza-Klein.  Structurally they differ:

  · **KK**: 5th axis is a *small-radius compactified circle*
    (metric residue at small scales).  Geometric / metric fact.
  · **213**: 5th axis is *not readout through chart-Lens*
    (structural absence of exterior per §8.1).  Lens-output fact,
    no metric, no compactification.

The failure mode "Stereotype matching" (`CLAUDE.md`) flags
KK-import as a primary risk for any future expansion of G121.
Specifically:
  · Do NOT introduce "compactification radius"
  · Do NOT introduce "extra-dimensional momentum modes"
  · Do NOT claim 213 "is" KK in disguise

The two pictures predict different things: KK predicts
KK-tower mass spectrum; 213 predicts level-cofinal exotic residue.
Distinguishing experiments (if any) close M4 empirically.

## §7 Validation routes

For G121 to promote from open conjecture to theorem candidate:

(R1) **Close M2 first**.  Formalize chart-Lens readout count =
$d_{213} - 1$.  This is the structural backbone.  Likely home:
new file in `lean/E213/Lens/` or extension of existing chart-Lens
material (e.g., `Lens/Number/Nat213/ChartGeneral.lean`).

**R1 partial progress (2026-05-22)**: definitional scaffold
committed at `lean/E213/Lib/Math/GeometrizationConjecture/
ChartAxisAnsatz.lean` (12 PURE).  Encodes the ansatz parametrically
in (NS, NT) with `selfPointingAxes := 1` as a `def`.  This is
*not* the real M2 close — it commits the ansatz to definitional
form so future work can either (a) upgrade `selfPointingAxes` from
`def` to a derived theorem, or (b) falsify the commitment by
exhibiting a 213-deployment with $\ne 1$ self-pointing axis.
Real M2 close requires linking §8.1 (no exterior) to chart-Lens
axiom-corpus at the Lens-ring level.

(R2) **Close M3 next**.  Derive (not match) the $N_T$-axis split
into time + self-pointing.  Likely route: $c = 2$ binary cover
analysis on T-side.

(R3) **M4 firewall**: write any further development with explicit
"this is not KK" anchor.  Stereotype matching is high-risk on this
topic; cite §6.4 in any expansion.

(R4) **M1 may stay open longer**.  Even with M1 unresolved,
closing M2+M3 yields a conditional theorem:

> *Given $d_{213} = 5$, $d_M = 4$ is forced and corresponds to
> the unique critical exotic-residue dimension.*

This conditional form is already useful.  Full unconditional
result requires M1.

## §8 Potential falsifier form

If R1-R3 close, the conjecture becomes:

> **Conjecture (G121-1)**: For any K_{NS, NT}^{(c)} deployment of
> 213 with fractal base $d = N_S + N_T$, the chart-Lens readout
> count is $d - 1$, and the critical exotic-residue manifold
> dimension is $d_M = d - 1$.

Falsifiable by:
  · Exhibiting a 213-deployment where chart-Lens readout count
    $\ne d_{213} - 1$.
  · Exhibiting an exotic-residue critical phenomenon at
    $d_M \ne d_{213} - 1$ in a 213-consistent deployment.
  · Exhibiting a deployment with $N_S + N_T \ne d_{213}$ but with
    consistent chart-Lens behavior.

None of these has been demonstrated.  The conjecture is currently
unfalsified but also unproven.

If proven, this would be the first 213-Lens result connecting
manifold topology to 213 deployment parameters — a falsifier
candidate for `DRLT Validation Standard` clause 2.

## §9 What this note is NOT

  · **Not a derivation.**  Ansatz + number matching, with knots
    explicit.
  · **Not a Lean theorem.**  No theorem in `lean/E213/`
    currently references this note's claims.
  · **Not a precision result.**  No numerical prediction with
    ppb~ppm precision.
  · **Not a falsifier yet.**  §8 outlines the falsifier form
    that would obtain if R1-R3 close.
  · **Not Kaluza-Klein in disguise.**  See M4.
  · **Not a universe-constant claim.**  $d_{213} = 5$ is the
    fractal base of the configCount family in the K_{3,2}^{(c=2)}
    deployment, not a privileged constant of 213 as a whole
    (per G120 Round 3 + §11 audit).
  · **Not a re-proof of Geometrization.**  213-Lens reads the
    Thurston/Perelman result through self-reference + chart
    + configCount; it does not replace or re-prove it.

## §10 Cross-references

### 213 internals
  · `seed/AXIOM/07_self_reference.md` §8.1 — no exterior
  · `seed/AXIOM/09_chart_relativity.md` — chart-Lens
  · `seed/INDEX.md` — naming policy
  · `CLAUDE.md` failure modes table — universe-constant framing,
    stereotype matching, dichotomy import

### Recent foundational notes
  · `research-notes/G120_n_u_rederivation_plan.md` — configCount
    family, retraction of N_U as constant
  · `theory/lens/cardinality.md` — frame-correct exemplar (per
    G120 §11.4)

### Lean reference points
  · `lean/E213/Lib/Math/Cohomology/Fractal/Level.lean` — `numV`
  · `lean/E213/Lib/Physics/Symmetry/C3ChainCapstone.lean` — gauge
    chain (possible $8 = 2^3$ ↔ 8 model geometries connection,
    speculative, not to force-match)

### Standard math
  · Thurston, *Three-dimensional manifolds, Kleinian groups and
    hyperbolic geometry*, Bull. AMS 6 (1982).
  · Perelman, arXiv:math/0211159, 0303109, 0307245 (2002-2003).
  · Freedman, *The topology of four-dimensional manifolds*, J.
    Diff. Geom. 17 (1982).
  · Donaldson, *Self-dual connections and the topology of smooth
    4-manifolds*, Bull. AMS 8 (1983).
  · Kervaire-Milnor, *Groups of homotopy spheres I*, Ann. Math.
    77 (1963).

## §11 Session origin (provenance)

This note records the narrative arc of session 2026-05-22 on
branch `claude/geometrization-conjecture-9Vf6i`:

  1. User asks for explanation of Geometrization conjecture in
     standard form and in 213-Lens (§1).
  2. User poses the dimension-4 exotic anomaly conjecture
     (§2.2) with the confinement / critical / smearing framing.
  3. First-pass 213-Lens response includes
     "$N_U = 5^{25}$ finite" — universe-constant framing import.
  4. User flags: merge `claude/research-notes-organization-Gr3Tp`
     and reconsider with G120.  G120 Round 3 + §11 audit
     internalized (§3).
  5. User sharpens with the $d_M = d_{213} - 1$ ansatz (§4.1).
  6. Knots M1-M4 surfaced; user requests record as G121 entry
     point for future work.
  7. User says "ㄱㄱ" (go ahead) on R1.  Definitional scaffold
     committed: `lean/E213/Lib/Math/GeometrizationConjecture/
     ChartAxisAnsatz.lean` (12 PURE theorems, ∅-axiom verified).
     Parametric in (NS, NT); K_{3,2}^{(c=2)} specialisation gives
     `chartVisibleAxes 3 2 = 4`; falsifier-candidate predictions
     for K_{2,2}, K_{4,2}, K_{3,3}.  **R1 not closed** — the file
     encodes the ansatz as a *definition* (`selfPointingAxes := 1`
     commits to the 1-axis claim); the structural derivation from
     §8.1 (no exterior) is still M2.

The narrative is preserved here so future sessions can resume the
thread without context loss.

---

**Next-session entry point**: derive `selfPointingAxes = 1` from
`seed/AXIOM/07_self_reference.md` §8.1 + chart-Lens axioms, i.e.,
upgrade `ChartAxisAnsatz.selfPointingAxes` from `def := 1` to a
theorem.  This is the *real* M2 close.  See §7 R1.

