# Decomposition: curvature / parallel transport / holonomy

*213-decomposition per `../README.md` (model v6). Builds directly on `noether.md` (the
`Aut(C)`-invariant character `det = 1` = conserved quantity) and `determinant.md` (the character
reading with sign = orientation) and `homology.md` (the `q=±1` direction bit governing two-step
composites). The LEVERAGE hypothesis to **derive**, not just re-see: parallel transport around a
**loop**, read as "how far from the identity", is the **holonomy**; curvature is its infinitesimal
**residue**. FLATNESS (curvature 0) = the holonomy det being the conserved character `det = 1` —
the SAME `det_holonomy_eq_one` Noether-invariant. So curvature = the `q=±1` residue of the
holonomy character; flat connection = `q=+1` conserved (`det = 1`); and the repo ties this to
gravity (Regge / Ricci). The leverage: the calculus *predicts* "flat = conserved-character = det 1"
and "curvature = the loop-reading's residue", unifying geometry with Noether/determinant via one
character.*

## The decomposition (C / Reading / Residue)

- **Construction `C`** — the same ×-construction of `noether.md`/`determinant.md`: `2×2` bundles of
  directed counts built by composition `mul`, now read as **state-transitions**. Without external
  time, a transition is not separable from the state it lands on (§6.6); a `Mat2` *is* that
  collapse — read frozen it is a configuration (four counts), read dynamically it is `x ↦ M·x`. A
  **path** is a `List Mat2` of transitions (`HolonomyLattice.holonomy`).

- **Reading `L_loop` (the loop-composition reading)** — fold a path to its **net transition**:
  `holonomy w = g₀·g₁·…·gₙ·I`. This is the genuine connection reading — it is a monoid
  homomorphism from the free monoid of paths `(List Mat2, ++)` to the matrix monoid `(Mat2, ·)`
  (`holonomy_append`), so transport composes functorially, and the codomain is *states* of the
  same kind: a loop of transitions composes to a state (the §6.6 collapse, computational). The
  **holonomy** is precisely "where the loop lands" — its distance from `I` is the readout.

- **Residue** — `q = ±1`, the orientation/multiplier bit of the holonomy character `det`. This is
  the *same* residue tag as `noether.md`/`homology.md`: the loop-reading is a character (`det` is
  multiplicative, `det_mul`), and **curvature is the surplus the flat reading cannot fill** — the
  deficit by which `holonomy w` fails to be `I`. The two poles: `q = +1` = the holonomy returns
  flat (`det = 1` conserved, curvature 0); `q = −1` = the **first non-trivial loop**, the fold
  `holonomy [S, S] = −I ≠ I`, the order-4 elliptic deficit. Curvature lives at the `q = −1` /
  deficit pole; flatness at `q = +1`.

## Re-seeing (⟨C | L⟩)

```
   parallel transport    =  ⟨ path (List Mat2 of transitions) | L_loop = the ordered fold-product ⟩
   "transport composes"  =  L_loop is functorial         (holonomy_append: monoid homomorphism)
   holonomy of a loop    =  holonomy w  — where the loop lands, read against I
   "flat connection"     =  the holonomy character det is conserved = 1   (det_holonomy_eq_one)
   curvature             =  Residue(L_loop, C):  the deficit by which holonomy w ≠ I  (q = −1 pole)
   "first curvature"     =  holonomy [S,S] = −I ≠ I   (first_loop_is_the_fold) — the q=−1 deficit
   flat ⟺ q = +1         =  det s n = qⁿ·det s 0, conserved ⟺ q=+1   (det_closed / cassini_law)
```

Set side by side with `noether.md` and `homology.md`, curvature is one corner of a single picture
on `C`'s `q=±1` direction axis:

| reading | what the loop/composite does | residue at `q=−1` |
|---|---|---|
| `det` Noether-invariant (`noether.md`) | character fixed under the `Aut`-action | conservation *fails* → alternation |
| `∂` boundary (`homology.md`) | two-step composite, signs cancel | `∂²=0` (nilpotent), residue = homology |
| **`L_loop` holonomy (here)** | **a loop composes to a net transition** | **curvature** = `holonomy ≠ I` deficit |

The holonomy is the *same character `det`* of `determinant.md`/`noether.md` propagated around a
loop instead of along a tree; curvature is what that propagation leaves un-cancelled. Flat = the
loop closes to `I` (the `q=+1`, det-conserved pole); curved = it lands at a deficit (`q=−1`).

## LEVERAGE — does flat = det1 = conserved-character, and curvature = loop-residue, fall out?

The answer splits the way `noether.md`'s did: **the structural skeleton is predicted and
Lean-built; the curvature *field* is conceptual / partial.** Honest, leg by leg.

**(1) Flat = conserved-character = det 1 — PREDICTED and CERTIFIED (the strong leg).** This is not
asserted; it is the *same* `det_holonomy_eq_one` invariant `noether.md` cites, now read as
geometry:

- transport is a genuine connection — `holonomy_append` makes it a monoid homomorphism (functorial
  parallel transport), ∅-axiom;
- flatness *is* the conserved character: `det_holonomy_eq_one` — if every step has `det = 1`, the
  holonomy has `det = 1` around *every* loop. The file's own header names this "the conserved
  holonomy invariant — the discrete flat connection." So **flat connection = the Noether-invariant
  character `det = 1`** is literally one theorem, shared with `noether.md`/`determinant.md`. The
  calculus *predicts* this identity (the flat readout must be the character, the only reading
  forced to be a homomorphism on `mul`) and Lean confirms the readouts coincide.
- the conserved-vs-deficit dichotomy is the parametric `q=±1` law: `det_closed`
  (`det s n = qⁿ·det s 0`), `cassini_law_one_at_two_multipliers` — flat ⟺ `q=+1`, deficit at
  `q=−1`. The same residue tag the README's model carries.

**(2) Curvature = the loop-reading's residue — PREDICTED at the deficit level, and built
discretely.** The hypothesis "curvature is the residue of a loop-reading" cashes cleanly at the
*combinatorial* level, two independent ways:

- **Holonomy deficit**: the first non-trivial loop is `holonomy [S, S] = −I ≠ I`
  (`first_loop_is_the_fold`), the order-4 elliptic deficit — the *exact* point where the flat
  reading's residue becomes nonzero. Curvature = "how far the loop lands from `I`", and the file
  proves the ℕ⁺ (tree) sector is *loop-free* (`positive_loop_trivial`) — flat — while admitting the
  sign-fold `S` (the `q=−1` bit) creates the first holonomy. So **curvature is born exactly as the
  residue of the loop-reading when the `q=−1` direction bit enters** — a clean instance of the
  `q=±1` residue.
- **Discrete curvature ↔ topology**, derived as a theorem: Forman curvature `4 − du − dv`
  (`forman_K11 = 2 > 0` tree, `forman_K32 = −1 < 0` cyclic; `discrete_curvature_topology`) and the
  **discrete Gauss–Bonnet** identity `Σκ = 2χ`, `total curvature = 2 − 2b₁`
  (`gauss_bonnet_Kmn`, `totalCurv_eq`, `curvature_sign_topology`). Curvature sign ⟺ `b₁` = the
  trivial-loop (flat, `q=+1`) vs rich-loop (curved, `q=−1`) split, *derived* not tabulated. This is
  the loop-residue read as topology: curvature positive ⟺ `b₁ = 0` ⟺ no nontrivial loop ⟺ flat
  holonomy — exactly the `positive_loop_trivial` (tree) / `first_loop_is_the_fold` (cyclic) split,
  re-proved on graphs.

**(3) The gravity bridge — PREDICTED as a generator identity, but thin as a curvature field (the
honest qualifier).** `MetricHolonomyBridge.metric_J_is_holonomy_S` proves, entry for entry, that
the gravity metric's complex structure `J = (0,−1,1,0)` (which builds `h = Q·J`) **is** the elliptic
holonomy generator `Mat2.S`, both squaring to `−I` (`signed_star_sq_neg_I`,
`first_loop_is_the_fold`). So "gravity = metric" (current 213) and "gravity = holonomy / deficit
angle" (Regge) are the *same* object — the calculus predicts the reconciliation and Lean fuses the
two proven matrices. **But its own CAVEAT is load-bearing**: this is a *generator identity*, not a
curvature *field*. A field needs a connection transporting `h` over a multi-simplex glued lattice;
the repo has only one flat `Δ⁴` (`h = I`) and no such connection. So the Regge "deficit = curvature
= metric" tie is structural, not a transported curvature tensor.

**The honest boundary (prediction vs collapse).** What the calculus genuinely *predicts*: (a) the
flat readout **must be the conserved character `det = 1`** (forced — the only homomorphism on
`mul`), shared verbatim with Noether; (b) curvature **is the loop-reading's residue at the `q=−1`
deficit pole**, born exactly when the sign-fold enters, and read as `b₁` via Gauss–Bonnet. What it
does **not** deliver: the smooth Riemann/Ricci *curvature tensor* and continuous parallel transport
of a varying metric — there is no smooth connection, no `R^ρ_{σμν}`, no Perelman flow (the
`DiscreteRicci` header flags this explicitly: "smooth Perelman is not treated; this is the discrete
parallel theory"). The continuous holonomy → curvature limit (the `lim_{loop→0} (holonomy − I)/area`
that *defines* curvature analytically) is the named open frontier, the geometry-side twin of
`noether.md`'s missing variational current.

**Verdict: PREDICTION (structural + discrete), short of the smooth curvature field.** Flat =
det1 = conserved-character is one Lean theorem (`det_holonomy_eq_one`), shared with Noether/det —
the calculus *predicts* the identity and Lean certifies the readouts coincide. Curvature = the
loop-reading's `q=±1` residue is built discretely two ways (holonomy deficit `holonomy[S,S]=−I`;
Gauss–Bonnet `Σκ=2χ`, `total = 2−2b₁`). The gravity/Regge tie is a proven *generator* identity
(`J = S`) with an honest CAVEAT (no curvature field, no connection over a glued lattice). The smooth
curvature tensor and the infinitesimal holonomy→curvature limit remain conceptual/open.

## Note for the technique — does curvature confirm "residue of a loop-reading" and tie geometry to the Noether/det character?

**YES, as a structural instance, and it is the cleanest tie of geometry to the character arrow so
far.** "Holonomy = the loop-composition reading, curvature = its residue" is a clean instance of
the `q=±1` residue, for three reasons:

1. **The reading is the same character, read around a loop.** Holonomy is `det`-the-character
   (`det_mul`, the `×↦·` arrow of `determinant.md`/`vp_mul`/parity `L₂`/entropy additivity)
   propagated along a *loop* rather than along the Stern–Brocot *tree*. Flatness = that character
   conserved (`det_holonomy_eq_one`) = `noether.md`'s `Aut`-invariant. So geometry adds **no new
   primitive**: the connection is the character reading, flatness is its conservation, and the
   single `×↦·` arrow now runs through geometry too.

2. **Curvature is the residue at the `q=−1` pole, and it is born from the direction bit.** Just as
   `homology.md`'s `∂²=0` is the `q=−1` direction bit cancelling pairwise, curvature is the `q=−1`
   bit *failing to cancel around a loop* — the deficit `holonomy[S,S]=−I`. The tree sector
   (`q=+1`, all `det=1`) is flat/loop-free (`positive_loop_trivial`); admitting the sign-fold `S`
   (the `q=−1` entry `S.b=−1`) creates the first curvature (`first_loop_is_the_fold`). So curvature
   and flatness are **one law at the two residue signs** — `det_closed`'s `qⁿ`, the same
   `cassini_law_one_at_two_multipliers` dichotomy. This is curvature as `Residue(L_loop, C)`,
   tagged `q=±1`, verbatim the model's residue structure.

3. **The geometry corner mirrors the homology corner exactly.** `homology.md` is the height-axis
   run *down* with the direction bit on, residue = homology; **curvature is the loop-reading with
   the direction bit on, residue = the holonomy deficit**. Both are the `q=−1` pole of one residue
   tag at a composite; both make a classical geometric object (homology class / curvature) into
   *the surplus of one reading*. Gauss–Bonnet `Σκ = 2χ = 2(1−b₁)` is the bridge: it ties curvature
   (the loop-residue) directly to `b₁` (the homology residue) — *one* residue, read as curvature on
   one side and as a cycle-count on the other.

So curvature **confirms** the derivable law *"flat = conserved character = det 1"* (shared with
Noether/determinant) and *"curvature = the loop-reading's `q=±1` residue"* (mirroring homology),
tying differential geometry to the single `×↦·` character arrow and the `q=±1` residue tag — a real
leverage at the structural + discrete level. The honest residual: the **smooth curvature tensor and
the continuous holonomy→curvature limit** are not built (the discrete theory is the parallel one),
and the gravity/Regge tie is a generator identity, not a transported field. Model v6 holds; no new
axis.

---

### Verified Lean anchors (file : theorem — all ∅-axiom-style pure `ℤ`/list identities, grep-checked on `lean/E213`)

| Leg | Theorem (file : name) | Status |
|---|---|---|
| parallel transport = functorial loop-reading | `Lib/Math/NumberSystems/Real213/ModularGeometry/HolonomyLattice.lean : holonomy`, `holonomy_append`, `det_holonomy_append` | ∅-axiom ✓ |
| ★ flat connection = conserved character `det = 1` (shared with `noether.md`) | `…/HolonomyLattice.lean : det_holonomy_eq_one`, `det_mul` | ∅-axiom ✓ |
| ★ curvature = loop-residue: tree loop-free vs first deficit `holonomy[S,S]=−I` (`q=±1`) | `…/HolonomyLattice.lean : positive_loop_trivial`, `positiveWord_entrySum_gt_two`, `first_loop_is_the_fold` | ∅-axiom ✓ |
| the `q=±1` conserved/deficit law: `det s n = qⁿ·det s 0`, conserved ⟺ `q=+1` | `Lib/Math/Algebra/CassiniUnimodular.lean : det_step`, `det_closed`, `cassini_law_one_at_two_multipliers` | ∅-axiom ✓ |
| ★ discrete curvature ↔ topology (loop-residue read as `b₁`) | `Lib/Math/Geometry/DiscreteCurvature/DiscreteRicci.lean : formanEdge`, `forman_K11`, `forman_K32`, `discrete_curvature_topology` | ∅-axiom ✓ |
| ★ discrete Gauss–Bonnet `Σκ = 2χ`, total `= 2 − 2b₁` (curvature-sign ⟺ topology) | `Lib/Math/Geometry/DiscreteCurvature/DiscreteGaussBonnet.lean : gauss_bonnet_Kmn`, `totalCurv_eq`, `curvature_sign_topology`, `forman_eq_vertexCurv_sum` | ∅-axiom ✓ |
| gravity/Regge tie: metric `J` IS holonomy generator `S` (deficit `S²=−I`) | `Lib/Physics/Cosmology/MetricHolonomyBridge.lean : metric_J_is_holonomy_S` (cites `signed_star_sq_neg_I`, `first_loop_is_the_fold`; own CAVEAT: no curvature field/connection) | structural identity ✓ (thin) |
| modulus carries Ricci alongside continuity/derivative/α_em (resolution axis) | `Lib/Math/Geometry/Topology/ModulusStructure.lean : four_way_modulus_framework`, `IsModulusStructure` (via `continuity.md`) | ∅-axiom ✓ (Ricci leg is the discrete flow) |
| cross-frame to the character arrow | `noether.md` (`det_holonomy_eq_one` as Noether-invariant), `determinant.md` (`det2_mul`, sign=orientation), `homology.md` (`q=±1` two-step composite) | prior, ∅-axiom ✓ |

### Dropped / unverified citations (honest)

- **CORRECTION (stale gap, fixed per `connections.md`):** an earlier version claimed "no Riemann/Ricci
  tensor, no `R^ρ_{σμν}`, no Bianchi, no Christoffel" — that is **false**. `Lib/Math/Geometry/TensorCalculus.lean`
  (23/0 PURE) builds the **abstract-index Riemann tensor** `riemUp` (`R^l_{ijk}`), Christoffel symbols of both
  kinds, Levi-Civita (`chris1_symm` torsion-free + `chris1_metric_compat` = `∇g=0`), Ricci (`ricciFromRiem`),
  scalar curvature, Einstein fixed-points, and **both first-Bianchi identities** (`riem_bianchi1`, the cyclic
  `q=−1` cancellation = the same mechanism as `jacobi`/`dsq_zero`), with `riem_antisym_jk` (the `q=−1`
  pair-swap). The genuine remaining residue is **strictly smaller**: only the **smooth metric** — `dg`/`Gam`
  are abstract `Int`-valued index fields carried by hypotheses, not the `Real213`-cut `h→0` derivatives of a
  differentiable metric — plus the un-welded `lim_{loop→0}(holonomy−I)/area` tying `holonomy` to `riemUp`.
  (The `DiscreteRicci` header's "smooth Perelman not treated" stands; the abstract tensor calculus does not.)
- **`MetricHolonomyBridge` cited with its CAVEAT**: a *generator identity* `J = S`, not a
  transported curvature field; flagged thin so the Regge tie is not overclaimed.
- **`four_way_modulus_framework`'s "Ricci" leg** is the *discrete* Ricci flow modulus, not smooth
  Perelman `𝓕/𝓦`-monotonicity; cited as the resolution-axis carrier, scope-honest.
