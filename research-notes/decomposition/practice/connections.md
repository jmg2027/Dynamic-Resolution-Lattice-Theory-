# Decomposition: connections & curvature (∇, parallel transport, holonomy, the Riemann tensor, Bianchi, Levi-Civita)

*213-decomposition per `../README.md` (model v7.1). The deepest consolidation in the geometry
cluster: it welds `curvature.md` (holonomy `L_loop`, the `q=±1` loop deficit, Gauss–Bonnet),
`fundamental_group.md` (holonomy as the loop-group / monodromy), `de_rham.md` (`d²=0` = telescope =
Stokes), and `lie_theory.md` (the bracket `[∇_X,∇_Y]`, the `q=−1` antisymmetry, Jacobi) into one
picture — and corrects a stale "missing leg" the four predecessors all recorded. The hypotheses to
**derive**, not re-skin:*

1. *a **connection ∇ / parallel transport** = the **holonomy reading** `L_loop` — transport around a
   path = composing the path's local frames (`holonomy_append`, a monoid homomorphism); flat = `det 1`
   (`det_holonomy_eq_one`). The connection is **how the loop-reading varies across the resolution
   lattice** — the comparison of nearby fibres.*
2. *curvature **R = holonomy around an infinitesimal loop** = the `q=±1` residue of the loop-reading
   (`first_loop_is_the_fold : holonomy[S,S] = −I ≠ I` — transport's failure to return `I` IS
   curvature). Flat (`R=0`) = `q=+1` (path-independent, the loop closes trivially); curved = `q=−1`
   (holonomy ≠ id).*
3. *curvature **= `[∇_X,∇_Y]` (the commutator of covariant derivatives)** = `lie_theory.md`'s bracket
   (`Mat2Bracket.bracket`, the `q=−1` antisymmetry). `R(X,Y) = [∇_X,∇_Y] − ∇_{[X,Y]}` — curvature is
   the bracket-residue of the connection. The double-tie (geometric loop AND algebraic commutator) is
   the leverage.*
4. *the **Bianchi identity** (`dR=0` / `∑ cyclic ∇R = 0`) = the `d²=0` / Jacobi cyclic-cancellation
   (`dsq_zero_universal_delta4`, `Mat2Bracket.jacobi`); **Gauss–Bonnet** `∫K = 2πχ` = `totalCurv_eq`
   (`Σκ = 2(1−b₁)`).*

## The decomposition (C / Reading / Residue)

- **Construction `C`** — two coincident faces of the *same* ×-construction, met at the
  fibre-comparison.
  - *The loop face* (the `curvature.md`/`fundamental_group.md` `C`): a **path** = `List Mat2` of
    state-transitions; without external time a transition is not separable from the state it lands on
    (§6.6), so a `Mat2` read frozen is a configuration (four counts) and read dynamically is `x ↦ M·x`.
    A **fibre** over a point is a copy of this state space; a **connection** is a rule for identifying
    nearby fibres — i.e. *which `Mat2` transports a frame one step*.
  - *The tensor face* (the new anchor, `TensorCalculus.lean`): the **connection coefficients**
    `Γ^l_{ij}` (`Gam l i j`) themselves — an abstract `Int`-valued index field, the local data of `∇`,
    with the metric entering through its derivative tensor `dg a b c = ∂_a g_{bc}` (`chris1x2`). The
    two faces are one `C` at two resolutions: the holonomy is the *finite* composite of the connection,
    `Γ` is its *infinitesimal* local form (the `lie_theory.md` "bracket = holonomy one order down" axis,
    now extended to the genuine `R = ∂Γ − ∂Γ + [Γ,Γ]`).

- **Reading `L_∇` (the connection / covariant-derivative reading)** — fold a path to its **net
  transport** `holonomy w = g₀·g₁·…·gₙ·I`, read against `I`. This is the genuine connection reading: a
  monoid homomorphism `(List Mat2, ++) → (Mat2, ·)` (`holonomy_append`), so transport composes
  functorially and the codomain is *states* of the same kind — a loop of transitions composes to a
  state (the §6.6 collapse, computational). The covariant-derivative form of the *same* reading is
  `∇`'s local coefficient `Γ`; the **comparison of nearby fibres** is exactly "how `L_∇` varies one
  step", and the curvature `R^l_{ijk} = ∂_jΓ^l_{ik} − ∂_kΓ^l_{ij} + Σ_m(Γ^l_{jm}Γ^m_{ik} −
  Γ^l_{km}Γ^m_{ij})` (`riemUp`) is the **antisymmetrized second variation** of that comparison — the
  commutator `[∇_j,∇_k]` made into an index field.

- **Residue** — `q = ±1`, the `ResidueTag` multiplier of the connection reading, read at the **loop**
  pole. Curvature is *the surplus the flat reading cannot fill* — the deficit by which transport fails
  to return `I`. Two poles, one law (`det_closed : det s n = qⁿ·det s 0`):
  - `q = +1` = **flat**: holonomy returns `I` (`det = 1` conserved, `det_holonomy_eq_one`,
    `positive_loop_trivial`), transport path-independent, `R ≡ 0` (`riem_flat`, `ricci_flat`,
    `scalar_flat`); the curvature commutator vanishes (`bracket_self : [A,A]=0`).
  - `q = −1` = **curved**: the first non-trivial loop `holonomy[S,S] = −I ≠ I`
    (`first_loop_is_the_fold`, order-4 elliptic deficit), born exactly when the sign-fold `S` (the
    `q=−1` bit, `S.b = −1`) enters; the curvature is the antisymmetric `[∇_j,∇_k]`
    (`riem_antisym_jk : R^l_{ijk} = −R^l_{ikj}`), the same `q=−1` pair-swap as `bracket_antisymm`.

## Re-seeing — ⟨C | L⟩ ⊕ Residue

```
   a connection ∇ / parallel transport  =  ⟨ path (List Mat2) | L_∇ = the ordered fold-product ⟩
                                            ⊕  local form Γ^l_{ij} (the comparison of nearby fibres)
   "transport composes" (functorial)     =  holonomy(p++q) = holonomy p · holonomy q   (holonomy_append)
   holonomy of a loop                    =  holonomy w, read against I
   "flat connection"  (R = 0, q=+1)      =  det holonomy = 1 conserved   (det_holonomy_eq_one)
                                            =  Γ ≡ 0 ⟹ R ≡ 0             (chris1_flat, riem_flat)
   curvature R = holonomy around a loop  =  Residue(L_∇, C): the deficit holonomy w ≠ I   (q = −1)
   "first curvature"                     =  holonomy[S,S] = −I ≠ I       (first_loop_is_the_fold)
   curvature R = [∇_j, ∇_k]              =  R^l_{ijk} = ∂_jΓ − ∂_kΓ + [ΓΓ−ΓΓ]   (riemUp)
   "R(j,k) = −R(k,j)"  (the q=−1 sign)   =  riem_antisym_jk            ≡  bracket_antisymm
   Levi-Civita (torsion-free, ∇g=0)      =  Γ_{kij}=Γ_{kji} (chris1_symm) + Γ+Γ=∂g (chris1_metric_compat)
   first Bianchi  ∑cyclic R = 0          =  cyclic q=−1 cancellation   (riem_bianchi1 ≡ jacobi shape ≡ ∂²=0)
   Gauss–Bonnet  ∫K = 2πχ                =  Σκ = 2(1−b₁)               (totalCurv_eq, gauss_bonnet_Kmn)
   flat ⟺ q=+1                           =  det s n = qⁿ·det s 0       (det_closed, cassini_law…)
```

Set side by side with the four cross-frames, connections-&-curvature is the corner where **all of
them meet** — it is the consolidation, not a sibling:

| reading | what the loop/composite does | residue at `q=−1` |
|---|---|---|
| `L_loop` holonomy (`curvature.md`) | a loop composes to a net transition | curvature = `holonomy ≠ I` deficit |
| `π₁` loop-group (`fundamental_group.md`) | loops compose, mod homotopy | non-contractible loop (`q=−1`) |
| `d`/`∂` fold-height (`de_rham.md`) | two-step composite, signs cancel | `d²=0` ≡ `∂²=0` (nilpotent) |
| `[,]` bracket (`lie_theory.md`) | two composition orders, read as a difference | `[X,Y]≠0` non-abelian |
| **`L_∇` connection (here)** | **transport varies across nearby fibres** | **R = `[∇_X,∇_Y]` = holonomy deficit** |

The connection is the *same character* `det` (`det_mul`, the `×↦·` arrow) propagated around a loop;
curvature is what that propagation leaves un-cancelled, read **two provably-equal ways** — as the
holonomy-around-a-loop deficit (`first_loop_is_the_fold`) AND as the commutator-of-covariant-
derivatives index field (`riemUp`/`riem_antisym_jk`). That is the double-tie.

## LEVERAGE — does curvature fall out as BOTH the holonomy-loop residue AND the bracket-commutator?

**Verdict: PREDICTION — and the geometry cluster's strongest, because a "missing leg" the four
predecessors all recorded is now CLOSED.** `curvature.md`, `de_rham.md`, and `lie_theory.md` each
named "the smooth Riemann/Ricci curvature tensor, no `R^ρ_{σμν}`, no Bianchi, no Christoffel" as the
open frontier. That is **stale**: `Lib/Math/Geometry/TensorCalculus.lean` (23/0 PURE) builds the
abstract-index Riemann tensor, Christoffel symbols (first + second kind), Levi-Civita metric
compatibility, Ricci, scalar curvature, AND both forms of the first Bianchi identity. The missing leg
shrinks to a strictly smaller, precisely-located residue (the *smooth* metric — §below). Leg by leg.

**(1) ∇ / parallel transport = the holonomy reading, flat = conserved character `det 1` — CERTIFIED.**
Not asserted; the *same* `det_holonomy_eq_one` invariant `noether.md`/`curvature.md` cite:
- transport is a genuine connection — `holonomy_append` makes it a monoid homomorphism (functorial
  parallel transport: `holonomy(p++q) = holonomy p · holonomy q`), PURE;
- flatness *is* the conserved character — `det_holonomy_eq_one`: every step `det = 1` ⟹ holonomy
  `det = 1` around *every* loop. The connection's "comparison of nearby fibres" is `L_∇` varying one
  step; the *flat* connection is where that comparison is the identity (path-independent transport).
- the conserved-vs-deficit law is the parametric `q=±1` (`det_closed : det s n = qⁿ·det s 0`,
  `cassini_law_one_at_two_multipliers`): flat ⟺ `q=+1`, deficit at `q=−1`.

**(2) ★ Curvature = holonomy around an infinitesimal loop = the `q=±1` loop residue — BUILT (the
first half of the double-tie).** The first non-trivial loop is `holonomy[S,S] = −I ≠ I`
(`first_loop_is_the_fold`), the order-4 elliptic deficit — the exact point where the flat reading's
residue becomes nonzero. The ℕ⁺ (tree) sector is loop-free (`positive_loop_trivial`,
`positiveWord_entrySum_gt_two`) — flat; admitting the sign-fold `S` (the `q=−1` bit) creates the first
holonomy. **Curvature is born exactly as the loop-reading's residue when the `q=−1` direction bit
enters.** Read as topology (`totalCurv_eq`): curvature sign ⟺ `b₁` (`gauss_bonnet_Kmn`,
`curvature_sign_topology`: `K_{1,1}` tree `+2`/`b₁=0`, `K_{3,2}` cyclic `−2`/`b₁=2`) — Gauss–Bonnet
`Σκ = 2(1−b₁)` ties the loop-residue directly to the homology residue.

**(3) ★★ Curvature R = `[∇_X,∇_Y]` = the bracket-commutator of covariant derivatives — BUILT (the
SECOND half of the double-tie; the new leverage).** This is the leg the predecessors could not cash,
and it now closes from BOTH sides:
- *Algebraic (finite commutator)*: `Mat2Bracket.bracket A B = AB − BA` (the connection's two
  transport orders read as a difference), with `bracket_antisymm : [A,B] = −[B,A]` — the `q=−1`
  pair-swap, the same sign as `det`/`∂`/ℤ. `R(X,Y) = [∇_X,∇_Y] − ∇_{[X,Y]}` is the bracket-residue:
  abelian/flat ⟹ `[X,Y]=0` (`bracket_self`); non-abelian/curved ⟹ `[X,Y]≠0`. (10/0 PURE.)
- *Geometric (the genuine index field)*: `TensorCalculus.riemUp` builds the Riemann tensor *literally*
  as `R^l_{ijk} = (∂_jΓ + Σ_m Γ^l_{jm}Γ^m_{ik}) − (∂_kΓ + Σ_m Γ^l_{km}Γ^m_{ij})` — the **commutator
  `[∇_j,∇_k]`** as a difference of the two orders, with `riem_antisym_jk : R^l_{ijk} = −R^l_{ikj}`
  (PURE, by `ring_intZ`) proving it antisymmetric in the differentiated pair — *the same `q=−1`
  antisymmetry as `bracket_antisymm`, now on the curvature index field*. `riem_flat`: `Γ≡0,∂Γ≡0 ⟹ R≡0`
  (`q=+1`). So curvature **= the antisymmetric commutator of the covariant derivative**, built, with
  the q=−1 sign forced. The double-tie holds: `first_loop_is_the_fold` (loop) and
  `riem_antisym_jk`/`riemUp` (commutator) are two readings of one `q=−1` residue.

**(4) ★ Bianchi = the cyclic q=−1 cancellation = Jacobi = `∂²=0` shape — BUILT.** `riem_bianchi1`
proves the first Bianchi identity `R^l_{ijk} + R^l_{jki} + R^l_{kij} = 0` (torsion-free, dimension-
free, PURE) by *exactly* the cyclic-cancellation `hexcancel : A−B+B−C+C−A = 0` — the **same
mechanism** as `Mat2Bracket.jacobi` (`[[A,B],C]+[[B,C],A]+[[C,A],B]=0`, the graded-Leibniz pole) and
`dsq_zero_universal_delta4` (the `q=−1` pairwise sign-cancellation). `riemLow_bianchi1` gives the
metric-2-jet form, alongside the four Riemann symmetries (`riemLow_antisym_ik/_lj`,
`riemLow_pair_symm`). So the Bianchi identity = `de_rham.md`'s `d²=0` / `lie_theory.md`'s Jacobi cyclic-
cancellation, *now proved on the curvature tensor itself* — not just cross-framed.

**(5) Levi-Civita = the metric-compatible torsion-free connection — BUILT.** `chris1_symm`
(`Γ_{kij}=Γ_{kji}`, torsion-free) and `chris1_metric_compat` (`Γ+Γ=∂g`, `∇g=0`) — the two identities
that *define* the Levi-Civita connection — are PURE (`ring_intZ`), with `chris2_lower` proving raising/
lowering consistency (`g·Γ² = det·Γ¹`) and `scalar_einstein` (`Ric=λg ⟹ R=λn`) the Einstein fixed-
point. So "the connection is metric and torsion-free" is a theorem, not a hypothesis.

**(6) Gauss–Bonnet `∫K = 2πχ` — BUILT (verbatim `curvature.md`/`de_rham.md`).** `totalCurv_eq`
(`Σκ = 2(1−b₁)`), `gauss_bonnet_Kmn` (`Σκ = 2χ`), `curvature_sign_topology` — the loop-residue read as
`b₁`, ∅-axiom.

**The honest boundary (prediction vs collapse).** What the calculus genuinely *predicts and now
closes*: (a) flat = conserved character `det 1` (forced — the only homomorphism on `mul`); (b)
curvature = the loop-reading's `q=−1` residue **AND** the antisymmetric commutator `[∇_j,∇_k]`
(`riemUp`/`riem_antisym_jk`), the double-tie; (c) Bianchi = the cyclic `q=−1` cancellation
(`riem_bianchi1`, same as Jacobi / `∂²=0`); (d) Levi-Civita = torsion-free + metric-compatible
(`chris1_symm`/`chris1_metric_compat`); (e) Gauss–Bonnet (`totalCurv_eq`).

**The precise remaining missing leg — the SMOOTH metric (strictly smaller than the predecessors
recorded).** `TensorCalculus`'s `Γ`, `R`, `Ric`, `dg`, `ddg`, `Gam` are abstract `Int`-valued index
fields (the metric enters only through hypotheses `dg a b c = ∂_a g_{bc}` symmetric, `g·adj=det·I`,
`∂∂` commuting). What is **absent** is the *smooth* metric `g_{ij}` as an actual differentiable
function over a manifold whose `Real213`-cut derivatives instantiate `dg`/`ddg` — i.e. the analytic
`h→0` completion (`derivative.md`'s general `Δ↔d/dx`, the `Real213`-cut residue). So the missing leg is
no longer "the Riemann tensor / Bianchi / Christoffel" (BUILT, abstract-index) — it is the **smooth
1-parameter metric bundle and its `h→0` derivative** the abstract index fields stand in for, the
*same* smooth-tensor gap as `de_rham.md`'s `Ω^k(M)`, `curvature.md`'s smooth holonomy→curvature limit,
and `lie_theory.md`'s tangent `ε²=0`. Likewise the *continuous* holonomy→curvature limit
(`lim_{loop→0}(holonomy−I)/area`) welding `holonomy` to `riemUp` is not built (the finite commutator
and the index field live in separate modules), and the metric-`J`-as-holonomy-generator tie
(`MetricHolonomyBridge.metric_J_is_holonomy_S`) is a *generator* identity, not a transported field.

## Revelation

**Collapse — the connection, parallel transport, curvature, the curvature commutator, Bianchi, and
Gauss–Bonnet are ONE reading at the `q=±1` poles, and curvature is provably the SAME `q=−1` residue
read two ways — geometric loop AND algebraic commutator — both built.** The single connection reading
`L_∇` on `C`, run as a loop and as a covariant-derivative index field, *generates all of differential
geometry's curvature machinery*:
- run as a **finite loop** → holonomy, flat = `det 1` conserved (`det_holonomy_eq_one`), curvature =
  the deficit `holonomy[S,S]=−I` (`first_loop_is_the_fold`), `q=±1`;
- run as the **covariant-derivative commutator** → `R^l_{ijk} = [∇_j,∇_k]` (`riemUp`), antisymmetric
  (`riem_antisym_jk`) by the *same* `q=−1` pair-swap as `bracket_antisymm` — **the two halves of the
  double-tie are now both ∅-axiom theorems**, where the predecessors had only the loop half;
- the **cyclic residue** → first Bianchi `∑cyclic R = 0` (`riem_bianchi1`), the *same* cyclic `q=−1`
  cancellation (`hexcancel`) as Jacobi (`Mat2Bracket.jacobi`) and `∂²=0` (`dsq_zero_universal_delta4`);
- the **metric-compatible torsion-free** specialization → Levi-Civita (`chris1_symm`,
  `chris1_metric_compat`), with Einstein fixed-points (`scalar_einstein`);
- the **loop-residue read as topology** → Gauss–Bonnet `Σκ = 2(1−b₁)` (`totalCurv_eq`).

This is the capstone of the README's "one character read N ways": `det` was scalar / `Aut`-invariant /
loop-holonomy / `∂`-down; connections-&-curvature adds the **covariant-derivative** reading and proves
its curvature is *literally* the `q=−1` antisymmetric commutator — so the geometric "curvature =
holonomy round a loop" and the algebraic "curvature = `[∇_X,∇_Y]`" are **one residue, two readings,
both certified**. The "no smooth Riemann tensor" frontier the four predecessors recorded is corrected:
the **abstract-index Riemann/Ricci/scalar/Bianchi/Christoffel tower is built (23/0 PURE)**; only the
*smooth metric's `h→0` derivative* (the `Real213`-cut completion) remains — the same single analytic
residue shared across the whole geometry cluster. **EXTEND by consolidation + a stale-leg correction;
no new axis; model v7.1 holds.**

## Note for the technique

- **The double-tie is the leverage: curvature is the `q=−1` residue read geometrically (loop) AND
  algebraically (commutator), and BOTH are now Lean theorems.** `first_loop_is_the_fold` (holonomy
  deficit) and `riemUp`/`riem_antisym_jk` (the `[∇_j,∇_k]` index field) are two readings of one
  residue — exactly the "two of the model's axes meeting" pattern the deepest results sit at (here:
  the `q=±1` direction bit meeting the resolution dial — finite loop vs infinitesimal `∂Γ`).
- **A recorded "missing leg" was stale — the calculus's frontier list must be re-audited against the
  repo.** Three notes (`curvature.md`, `de_rham.md`, `lie_theory.md`) named the smooth Riemann tensor /
  Bianchi / Christoffel as absent; `TensorCalculus.lean` (23/0 PURE) builds the abstract-index version
  of all three. The genuine residue is strictly smaller (the smooth metric's `h→0` derivative). This is
  the repo-first discipline biting: grep before declaring a gap.
- **Bianchi joins Jacobi and `∂²=0` as the third instance of the cyclic `q=−1` cancellation, proved on
  its own object.** `riem_bianchi1`'s `hexcancel` is the same `A−B+B−C+C−A=0` mechanism — the calculus's
  graded-relation / cyclic-cancellation slot, now spanning cohomology (`∂²=0`), Lie theory (Jacobi),
  and differential geometry (Bianchi) with one shape.

---

### Verified Lean anchors (file:line — all grep + `tools/scan_axioms.py`-verified this session; all PURE)

| Leg | Theorem (file : name : line) | Status |
|---|---|---|
| ∇ / parallel transport = functorial holonomy reading | `Lib/Math/NumberSystems/Real213/ModularGeometry/HolonomyLattice.lean : holonomy` (:93), `holonomy_append` (:108), `det_holonomy_append` (:325) | **PURE (scanned 26/0)** ✓ |
| ★ flat connection = conserved character `det = 1` (shared with `noether.md`/`curvature.md`) | `…/HolonomyLattice.lean : det_holonomy_eq_one` (:136), `det_mul` (:123) | **PURE** ✓ |
| ★ curvature = holonomy-loop residue: tree loop-free vs first deficit `holonomy[S,S]=−I` (`q=±1`) | `…/HolonomyLattice.lean : positive_loop_trivial` (:292), `positiveWord_entrySum_gt_two` (:276), `first_loop_is_the_fold` (:313) | **PURE** ✓ |
| the `q=±1` conserved/deficit law `det s n = qⁿ·det s 0`, conserved ⟺ `q=+1` | `Lib/Math/Algebra/CassiniUnimodular.lean : det_step` (:123), `det_closed` (:142), `cassini_law_one_at_two_multipliers` (:163) | **PURE** ✓ |
| ★★ curvature R = `[∇_j,∇_k]` index field `R^l_{ijk}=∂Γ−∂Γ+[ΓΓ−ΓΓ]`; antisymmetric (`q=−1`) | `Lib/Math/Geometry/TensorCalculus.lean : riemUp` (:135), `riem_antisym_jk` (:143, `R^l_{ijk}=−R^l_{ikj}`), `riem_flat` (:151) | **PURE (scanned 23/0)** ✓ |
| ★★ curvature = bracket-commutator `[A,B]=AB−BA`, antisymmetric (`q=−1`), self-bracket 0 (flat) | `Lib/Math/NumberSystems/Real213/Mat2/Mat2Bracket.lean : bracket` (:66), `bracket_antisymm` (:76), `bracket_self` (:86), `tr_bracket_zero` (:101) | **PURE (scanned 10/0)** ✓ |
| ★ first Bianchi `∑cyclic R = 0` = cyclic q=−1 cancellation = Jacobi = `∂²=0` shape | `Lib/Math/Geometry/TensorCalculus.lean : riem_bianchi1` (:186, `hexcancel`), `riemLow_bianchi1` (:249) | **PURE** ✓ |
| Jacobi (the same cyclic q=−1 cancellation, algebra side) | `…/Mat2/Mat2Bracket.lean : jacobi` (:118), `bracket_leibniz` (:135) | **PURE** ✓ |
| `d²=0` ≡ `∂²=0` (the cohomology face of the same cancellation) | `Lib/Math/Cohomology/Delta/V4Capstone.lean : dsq_zero_universal_delta4` (:41), `leibniz_universal_delta4` (:62) | **PURE (scanned)** ✓ |
| ★ Levi-Civita: torsion-free (`Γ_{kij}=Γ_{kji}`) + metric-compatible (`∇g=0`) | `Lib/Math/Geometry/TensorCalculus.lean : chris1_symm` (:48), `chris1_metric_compat` (:57), `chris1_flat` (:66), `chris2_symm` (:86), `chris2_lower` (:96) | **PURE** ✓ |
| Riemann symmetries (metric-2-jet form) + Ricci + scalar + Einstein fixed-point | `…/TensorCalculus.lean : riemLow_antisym_ik` (:224), `riemLow_antisym_lj` (:229), `riemLow_pair_symm` (:236), `ricciFromRiem` (:163), `ricci_flat` (:170), `scalar_einstein` (:281), `perelman_rate_nonneg` (:322) | **PURE** ✓ |
| ★ Gauss–Bonnet `Σκ = 2χ`, total `= 2−2b₁` (curvature-sign ⟺ topology) | `Lib/Math/Geometry/DiscreteCurvature/DiscreteGaussBonnet.lean : gauss_bonnet_Kmn` (:42), `totalCurv_eq` (:53), `euler_eq_one_sub_b1` (:47), `curvature_sign_topology` (:59), `forman_eq_vertexCurv_sum` (:71) | **PURE** ✓ |
| `q=±1` residue tag (flat = converge `q=+1` / curved = escape `q=−1`) | `Lib/Math/Foundations/ResidueTag.lean : ResidueTag` (:73), `multiplier` (:81), `escape_residue_outside`, `converge_residue_fixed` | **PURE** ✓ |
| cross-frame | `curvature.md` (`det_holonomy_eq_one`, `first_loop_is_the_fold`), `fundamental_group.md` (holonomy = loop-group), `de_rham.md` (`d²=0`=telescope), `lie_theory.md` (bracket, Jacobi) | prior, ∅-axiom ✓ |

### Conceptual-only legs / the precise remaining break (honest — NOT cited as built)

- **The SMOOTH metric `g_{ij}` as a differentiable function over a manifold — ABSENT (the one
  remaining leg).** `TensorCalculus`'s `dg`/`ddg`/`Gam`/`adj` are abstract `Int`-valued index fields
  with the metric structure carried by hypotheses (`dg a b c = ∂_a g_{bc}` symmetric, `g·adj=det·I`,
  `∂∂` commuting). There is no `Real213`-cut smooth metric whose `h→0` derivatives instantiate them —
  the same smooth-tensor / `h→0` residue as `de_rham.md`'s `Ω^k(M)`, `curvature.md`'s holonomy→curvature
  limit, `lie_theory.md`'s tangent `ε²=0`, `derivative.md`'s general `Δ↔d/dx`. **This is strictly
  smaller than the predecessors' recorded leg** ("no Riemann tensor / Bianchi / Christoffel" — now
  BUILT, abstract-index, 23/0 PURE); only the analytic completion remains.
- **The continuous holonomy→curvature limit `lim_{loop→0}(holonomy−I)/area` welding `holonomy` to
  `riemUp`** — not built. The finite commutator (`Mat2Bracket`/`HolonomyLattice`) and the index field
  (`TensorCalculus`) live in separate modules; the analytic identification that they are the
  infinitesimal/finite faces of one connection is the `h→0` residue, named not built.
- **`MetricHolonomyBridge.metric_J_is_holonomy_S`** — a *generator* identity (`J = S`, both squaring to
  `−I`), cited with `curvature.md`'s CAVEAT: a transported curvature *field* over a glued lattice is
  absent.
- **No `Connection`/`ParallelTransport`/`CovariantDerivative` named object** unifying the holonomy
  (finite) and `Γ`/`riemUp` (infinitesimal) faces — they are proven separately and cross-framed here,
  not welded into one structure (the promotion target).
