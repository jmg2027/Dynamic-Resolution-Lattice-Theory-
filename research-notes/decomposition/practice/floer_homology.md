# Decomposition: Floer homology (Morse theory on an infinite-dimensional functional — the symplectic action / Chern–Simons functional, critical points = periodic orbits / flat connections, the Floer differential counts J-holomorphic / ASD trajectories, ∂²=0, HF = ker∂/im∂, the Arnold conjecture)

*213-decomposition per `../README.md` (model v7.1). A **fresh** field, but a pure consolidation: it is
`morse_theory.md`'s residue machine **lifted to an infinite-dimensional functional**, fused with
`symplectic_geometry.md`'s det=1 conserved-orbit corner. Tests one composite thesis: Floer homology =
**Morse theory (`morse_theory.md`) on the symplectic-action / Chern–Simons functional** — the SAME
`ker∂/im∂` residue machine, with critical points = periodic Hamiltonian orbits / flat connections
(`symplectic_geometry.md`'s q+1 conserved sector), the Floer differential = the SAME `q=±1`
gradient-flow count (now counting J-holomorphic cylinders / ASD instantons instead of finite-dim
gradient lines), `∂²=0` the SAME `dsq_zero_universal_delta4`, and the Arnold conjecture =
`morse_theory.md`'s Floer=Morse=singular two-readings-one-residue + the Morse weak inequality
(#orbits ≥ #cells). The bar is PREDICTION/CONSOLIDATION (collapse of `morse_theory.md` +
`symplectic_geometry.md` onto one infinite-dim object), with the named `Floer`/`Arnold`/`Maslov`/
`Conley–Zehnder`/`JHolomorphic`/`ASD` objects honestly ABSENT and the ∞-dim moduli of J-holomorphic
curves the genuine `Real213`/analytic break.*

## The decomposition (C / Reading / Residue)

- **Construction `C` — the same cell/nesting build `morse_theory.md`/`homology.md` read, now with the
  height function `f` replaced by an infinite-dimensional *action functional*.** Floer homology
  introduces **no new construction**. `C` is still the build-tree of iterated distinguishing carrying
  `morse_theory.md`'s two read-off axes — a **fold-height** (the depth-count `Raw.depth`) and a
  **direction/orientation bit `q=±1`** (the removal/ordering sign). The single change from
  `morse_theory.md` is *which* real-valued functional grades the complex: the **symplectic action**
  `𝒜_H(γ) = ∫ γ*λ − ∫ H(γ(t))dt` on the loop space `LM` (Hamiltonian Floer), or the **Chern–Simons
  functional** `CS(A)` on the space of connections (instanton Floer). Both are functionals on an
  *infinite-dimensional* configuration space, but the calculus reads them through the *same finite
  signature* `morse_theory.md` uses — the critical-point set graded by an index, with `∂` a flow-line
  count. There is **no smooth manifold, no loop space `LM`, no Banach moduli of curves** in `C` — the
  construction is the combinatorial complex graded by the action's critical values, exactly the
  `Cochain n k` complex of `homology.md` with `k` the (Conley–Zehnder/Maslov) index grade. *The
  infinite-dimensionality lives entirely in the configuration space the functional is defined on, not in
  the residue machine that reads it* — which is the whole point.

- **Reading `L↑𝒜` (the action / Morse-on-`LM` reading)** — read `C` through the action functional's
  *value* and, at its flat spots, through its *index*. A **critical point of 𝒜** is where the
  distinguishing-direction reading (the `L²`-gradient `∇𝒜`, "which way does the action descend")
  **vanishes** — and the vanishing of `∇𝒜_H` is *exactly* the Hamilton's-equation condition
  `γ̇ = X_H(γ)`, so **critical points of the symplectic action = 1-periodic Hamiltonian orbits**
  (`symplectic_geometry.md`'s q+1 conserved flow: `Ḣ = {H,H} = 0`); critical points of Chern–Simons =
  **flat connections** (`F_A = 0`, `det_holonomy_eq_one`'s flatness condition). The **Conley–Zehnder /
  Maslov index** of a critical point = the number of "negative" directions = `morse_theory.md`'s
  **Morse index** = `dimension.md`'s fold-height grade `L↑` (`Raw.depth`), read at the action's flat
  spots. So `L↑𝒜` is `morse_theory.md`'s height-reading `L↑f` with `f` instantiated as `𝒜`/`CS` — not
  a new reading, the same height-reading conditioned on where the direction-bit reading nulls out, now
  on an ∞-dim domain.

- **Reading `∂𝒜` (the Floer differential, the J-holomorphic/ASD flow count)** — the Floer differential
  `∂(orbit_λ) = Σ (# J-holomorphic cylinders) · orbit_{λ−1}` (Hamiltonian) /
  `∂(conn_λ) = Σ (# ASD instantons) · conn_{λ−1}` (instanton) peels one index = drops the fold-height by
  one = `homology.md`'s boundary `∂` (the `delta` op read DOWN in grade), with the flow-line count
  carrying the `(−1)` orientation sign (`SignedCup.cup1_antisymmetric`). The J-holomorphic cylinder /
  ASD instanton **is the gradient-flow trajectory of the action functional** — a path connecting two
  critical points along `−∇𝒜`, exactly `morse_theory.md`'s `∂f` (gradient-flow count) on an ∞-dim
  functional. So `∂𝒜` is literally `morse_theory.md`'s `L↓` — the height-axis run downward with the
  direction bit on — and `∂𝒜² = 0` (the boundary of the 1-dim moduli of broken flows cancels in
  oriented pairs) is the SAME pairwise `q=−1` sign-cancellation as `∂²=0`/`dsq_zero_universal_delta4`.

- **Residue** — `q=±1` (the README's residue tag, `ResidueTag.lean`), at the two faces that are one:
  1. *Homology face:* `∂𝒜` has a kernel/image gap, and that gap IS Floer homology
     `HF_* = ker ∂𝒜 / im ∂𝒜` = closed-not-exact = "what the action-reading forces (cycles) but cannot
     fill one grade down (boundaries)". **Floer homology ≅ singular homology** is exactly
     `morse_theory.md`'s "Morse homology = singular homology" lifted: the Floer complex (generators =
     periodic orbits / flat connections, graded by Conley–Zehnder index) and the singular/cell complex
     (generators = cells, graded by dimension) compute the same `Residue(L↓,C)` —
     `BettiKernel.reduced_betti_d4_contractible` makes the empty/contractible case literal, and
     `NonzeroBetti.betti_one_cycle` the nonzero (`q=−1` escape) case.
  2. *Critical-point face:* a periodic orbit / flat connection is the **residue of the gradient
     reading** — the diagonal spot where `∇𝒜` self-points and vanishes, the `q=±1` place the
     action-reading cannot resolve into a single descending direction. `q=+1` converge pole: the
     downward flow `ẋ = −∇𝒜` reaches a critical point (`GradientFlow.gradient_descent_monotone`,
     `MonovariantFlow.flow_reaches`); `q=−1` escape pole: index-`>0` orbits are the un-fillable closed
     cycles forced on a topologically non-trivial space
     (`OneDiagonal.no_surjection_of_fixedpointfree` — the diagonal cannot be dodged).

## Re-seeing — ⟨C | L⟩ ⊕ Residue

```
   the action functional 𝒜_H        =  ⟨ build-nesting | L↑ on the loop space ⟩  =  morse_theory.md's f, now on LM (∞-dim domain, finite signature)
   crit pt of 𝒜_H = ∇𝒜=0           =  Hamilton's eq γ̇=X_H(γ)  =  a 1-periodic orbit  =  symplectic_geometry.md's q+1 conserved flow ({H,H}=0)
   crit pt of CS = ∇CS=0            =  F_A=0  =  a flat connection  =  det_holonomy_eq_one's flatness (instanton Floer)
   Conley–Zehnder / Maslov index μ  =  ⟨ build-nesting | L↑=depth ⟩ at the flat spot  =  morse_theory.md's Morse index  (Raw.depth)
   the Floer differential ∂𝒜         =  homology.md's ∂ (delta read DOWN), J-holo-cylinder/ASD count = the (−1) sign  =  morse_theory.md's ∂f
   "∂𝒜² = 0"                        =  broken J-holo flows cancel in oriented pairs  =  SAME q=±1 sign-cancel as ∂²=0  (dsq_zero_universal_delta4)
   HF_* = ker ∂𝒜 / im ∂𝒜            =  Residue(L↓,C), q=±1  =  morse_theory.md's HM_*  (the residue machine, lifted)
   "Floer homology ≅ singular"      =  morse_theory.md's "Morse = singular": orbit-complex = cell-complex, ONE residue  (reduced_betti_d4_contractible)
   Arnold: #periodic orbits ≥ #cells = HF≅H^sing (two readings, one residue) + the Morse weak ineq c_i ≥ b_i  (|gens| ≥ |ker/im|)
   "f contractible ⟹ one orbit"      =  q=+1 converge pole, residue empty  (reduced_betti_d4_contractible)
   index-μ orbit survives in HF      =  q=−1 escape pole, un-fillable cycle  (NonzeroBetti.betti_one_cycle)
```

Set against the cross-frames, **every row is a `morse_theory.md` row with the height function `f`
replaced by the action functional `𝒜`/`CS`**: the index row is `dimension.md`'s `Raw.depth`; the
`∂𝒜²=0` row is `homology.md`'s `dsq_zero_universal_delta4`; the HF≅singular row is `morse_theory.md`'s
Morse=singular = `de_rham.md`'s "two readings, one residue"; the critical-point-as-gradient-residue row
is the `OneDiagonal`/`GradientFlow` engine. The *only* new datum is **what the critical points are** —
periodic orbits / flat connections, i.e. `symplectic_geometry.md`'s q+1 conserved sector — and **what
the flow lines are** — J-holomorphic cylinders / ASD instantons, i.e. the gradient trajectories on an
∞-dim functional.

| classical Floer object | = the 213 reading | already in note | Lean anchor |
|---|---|---|---|
| critical point of 𝒜_H = periodic orbit | `symplectic_geometry.md`'s q+1 conserved flow (`{H,H}=0`); the gradient diagonal's residue | `symplectic_geometry.md`, `morse_theory.md` | `NoetherCurrent.density_conserved_of_det_one`, `OneDiagonal.no_surjection_of_fixedpointfree` |
| critical point of CS = flat connection | `det_holonomy_eq_one`'s flatness (`det=1` around every loop) | `gauge_theory.md` (parallel), `curvature.md` | `HolonomyLattice.det_holonomy_eq_one`, `first_loop_is_the_fold` |
| Conley–Zehnder / Maslov index μ | the fold-height grade `L↑` (`Raw.depth`) at the flat spot — `morse_theory.md`'s Morse index | `morse_theory.md`, `dimension.md` | `Lambek.isPart_wf`, `Levels.Raw.depth_slash` |
| Floer differential `∂𝒜` (J-holo / ASD count) | `homology.md`'s `∂` (`delta` read DOWN), flow count = `(−1)` sign | `morse_theory.md`, `homology.md` | `Delta/V4Capstone`, `SignedCup.cup1_antisymmetric` |
| `∂𝒜² = 0` (broken flows cancel) | the `q=±1` orientation sign-cancel, SAME theorem as `∂²=0` | `morse_theory.md`, `homology.md` | `V4Capstone.dsq_zero_universal_delta4` |
| Floer homology `ker∂𝒜/im∂𝒜` | `Residue(L↓,C)`, `q=±1` | `morse_theory.md`, `homology.md` | `BettiKernel.reduced_betti_d4_contractible`, `kerSizeDelta` |
| Floer homology ≅ singular homology | `morse_theory.md`'s "Morse = singular" (two readings, one residue) | `morse_theory.md`, `de_rham.md` | `reduced_betti_d4_contractible`, `NonzeroBetti.betti_one_cycle` |
| Arnold conjecture (#orbits ≥ #cells) | HF≅H^sing + Morse weak ineq `c_i ≥ b_i` (count ≥ residue dim) | `morse_theory.md` | `reduced_betti_d4_contractible` + `NonzeroBetti` (the data) |
| `−∇𝒜` flow reaches a critical point | the `q=+1` converge pole (fixed point reached) | `morse_theory.md` | `GradientFlow.gradient_descent_monotone`, `MonovariantFlow.flow_reaches` |

## LEVERAGE — does the hypothesis fall out, and what is built vs absent?

**Verdict: PREDICTION + the deepest CONSOLIDATION the homology cluster admits — Floer homology is
`morse_theory.md`'s residue machine reused *verbatim* on an infinite-dimensional functional; every leg
is an already-built ∅-axiom theorem, the *only* new content is the identification of the critical points
(periodic orbits / flat connections, `symplectic_geometry.md`) and the flow lines (J-holomorphic / ASD
trajectories); what is ABSENT is the *named* `Floer`/`Arnold`/`Maslov`/`Conley–Zehnder`/`JHolomorphic`/
`ASD` object (grep-confirmed: zero hits in `lean/E213`), and the genuine break is the ∞-dim moduli of
J-holomorphic curves (the analytic `Real213`/Banach corner).** Leg by leg, honest.

**(1) The Conley–Zehnder / Maslov index IS `morse_theory.md`'s Morse index = `dimension.md`'s
fold-height grade — GROUNDED.** The CZ/Maslov index `μ` (the spectral flow / number of negative
directions of the Hessian of `𝒜` at a critical point) is the ∞-dim replacement for the Morse index, and
`morse_theory.md` already grounds the Morse index = `dimension.md`'s height-reading `L↑` = `Raw.depth`,
**forced** (not chosen) by the well-founded build measure `Lambek.isPart_wf` (PURE) and the one-step law
`Raw.depth_slash` (`1+max`). The CZ index is the same `L↑` read at the flat spots of `𝒜`/`CS`. The ∞-dim
twist — that the *absolute* Morse index is infinite (every critical point of `𝒜` has infinitely many
ascending and descending directions), so only the *relative* index `μ(x)−μ(y)` is finite — is exactly
the "finite signature" rule (`README`'s modulus): the calculus reads the *difference of heights* (a
finite grade), never the absolute infinite height. No new primitive — the index is the relative
fold-height grade the build carries.

**(2) `∂𝒜² = 0` IS `morse_theory.md`/`homology.md`'s `∂²=0` — the SAME `q=±1` sign-cancellation,
PURE.** The Floer differential counts J-holomorphic cylinders (Hamiltonian) / ASD instantons (instanton)
between consecutive CZ indices; `∂𝒜²=0` holds because the compactified 1-dim moduli space of broken
flow lines has boundary = pairs of broken trajectories with *opposite* orientation that cancel — the
same pairwise `q=−1` orientation cancellation `morse_theory.md` grounds as
`V4Capstone.dsq_zero_universal_delta4` (`∀ σ, ∀ i, δ(δσ) i = false` on Δ⁴; **5 pure / 0 dirty**). The
signed reason (order-swap flips the sign) is `SignedCup.cup1_antisymmetric` (the `(−1)^inv` orientation
bit; **14 pure / 0 dirty**). So `∂𝒜²=0` is **not a fourth thing** — it is the direction bit's pairwise
cancellation, the `q=−1` pole, identical to `∂²=0`. *The hard analysis Floer theory does to PROVE `∂²=0`
— gluing, compactness of the cylinder moduli, transversality — is the construction of the count; the
algebraic identity it lands on is `dsq_zero`.*

**(3) ★ Floer homology ≅ singular homology IS `morse_theory.md`'s "two readings, one residue" — GROUNDED
as the load-bearing collapse.** The Floer complex (generators = periodic orbits / flat connections,
graded by CZ index) and the singular/cell complex (generators = cells, graded by dimension) compute the
**same** `ker/im` residue. This is exactly `morse_theory.md`'s Morse=singular statement lifted to the
∞-dim functional: two complexes built by different readings of the *same* `C` measure ONE
`Residue(L,C)`. `BettiKernel.reduced_betti_d4_contractible` (`kerSizeDelta 5 0 = 1 ∧ kerSizeDelta 5 1 =
2`; **11 pure / 0 dirty**) makes the empty case literal — on the contractible Δ⁴, `ker δ = im δ`,
residue empty, precisely "a Hamiltonian with one orbit on a contractible piece". The nonzero case — a
genuine un-fillable cycle (an index-`i` orbit surviving in homology) — is `NonzeroBetti.betti_one_cycle`
/ `cycle_vs_contractible_qpm` (the hollow triangle `S¹`, `b₁=1`; **56 pure / 0 dirty**), the `q=−1`
escape pole. So "Floer homology ≅ singular homology" stops being a deep PDE theorem and becomes the
README's residue read through two gradings of one `C`.

**(4) ★ The Arnold conjecture IS `morse_theory.md`'s Floer=singular + the Morse weak inequality —
GROUNDED.** The Arnold conjecture (a non-degenerate Hamiltonian has at least as many 1-periodic orbits
as a Morse function has critical points, i.e. `# orbits ≥ Σ b_i` / `c_i ≥ b_i`) decomposes into exactly
two prior pieces:
- **HF ≅ H^sing** (leg 3) — Floer homology is *independent of H* and equals the singular homology of the
  manifold (`morse_theory.md`'s reading-invariance: the alternating fold / the `ker/im` residue is the
  same whichever complex computes it).
- **the Morse weak inequality** `c_i ≥ b_i` — the number of index-`i` critical points (orbits) is at
  least the `i`-th Betti number, because `b_i = dim(ker ∂𝒜 / im ∂𝒜)` is a *subquotient* of the
  generator space, so `# generators ≥ dim of the residue`. This is verbatim `morse_theory.md`'s weak
  Morse inequality (`b_i = |ker/im| ≤ |gens| = c_i`), the residue-dimension bound.

So Arnold = (HF=singular, two readings one residue) + (count ≥ residue dimension) — *the same two
ingredients as the Morse inequalities*, now on the orbit-generated complex. The data are PURE on Δ⁴
(`BettiKernel` 11/0, `NonzeroBetti` 56/0, `FaceTerms` 10/0). ⚠ **Same category-error caveat as
`morse_theory.md`:** the bound is *dimension*-level — `kerSizeDelta n k` is the cocycle-space
*cardinality* `2^(dim ker δ_k)`, so the naive count form `kerSizeDelta 5 k ≤ binom 5 k` is **false** for
`k≥2` (`kerSizeDelta 5 2 = 16 > binom 5 2 = 10`); the faithful statement is `b_i ≤ dim ker δ_i ≤ c_i`,
needing the `log₂`-dimension extraction. The Euler *equality* `Σ(−1)^i c_i = χ = Σ(−1)^i b_i` (the count
form, clean `decide`) is `FaceTerms.simplex_face_euler_zero` (**10 pure / 0 dirty**).

**(5) ★ Periodic orbits / flat connections ARE the residue of the gradient reading, fused with
`symplectic_geometry.md`'s conserved sector — GROUNDED at both `q=±1` poles.** A periodic orbit is where
`∇𝒜_H = 0`, which is Hamilton's equation `γ̇ = X_H(γ)` — and `symplectic_geometry.md` certifies the
conserved-along-flow shape: `Ḣ = {H,H} = 0` is `NoetherCurrent.noether_local` (Aut-invariant ⟺
`det g = 1`) + `bracket_self = 0`, with phase-volume preservation `density_conserved_of_det_one` (**14
pure / 0 dirty**). A flat connection is where `∇CS = 0`, i.e. `F_A = 0` — `det = 1` around every loop,
verbatim `HolonomyLattice.det_holonomy_eq_one` (**26 pure / 0 dirty**), with `first_loop_is_the_fold`
the first non-trivial holonomy class. So the critical points of the Floer functional are
`symplectic_geometry.md`'s q+1 conserved objects. As a *residue* they carry both poles:
- *`q=+1` converge:* the downward action flow `ẋ = −∇𝒜` flows to a critical point (a fixed point
  reached) — `GradientFlow.gradient_descent_monotone` (`F(x−τ∇F) = F(x) − τ(1−τ)‖∇F‖²`, **9 pure / 0
  dirty**) and the well-founded reach `MonovariantFlow.flow_reaches` (**19 pure / 0 dirty**). The
  action-minimizing orbit is the `q=+1` fixed point.
- *`q=−1` escape:* index-`>0` orbits are un-dodgeable — on a topologically non-trivial manifold the
  gradient *must* vanish at extra critical points (the `q=−1` "the diagonal cannot be dodged" of
  `OneDiagonal.no_surjection_of_fixedpointfree` **11 pure / 0 dirty**, and
  `FlatOntologyClosure.object1_not_surjective`/`self_covering_closure` **7 pure / 0 dirty**). This is the
  Arnold mechanism: a non-zero homology count *forces* an orbit — `b_i > 0 ⟹ c_i > 0` — the same
  diagonal read with a count weight.

The README's `q=±1` tag is the formal home (`ResidueTag.residue_tag_two_poles`,
`escape_residue_outside`/`converge_residue_fixed`, `golden_is_converge`, `multiplier_unimodular`; **55
pure / 0 dirty**): the minimizing orbit = `q=+1` converge, the extra orbits/saddles = `q=−1` escape.

**Honest boundary — Lean-built vs conceptual.**
- *Lean-built (∅-axiom, scanned PURE this session):* (a) the CZ/Maslov index = the fold-height grade
  (`Lambek.isPart_wf`, `Levels.Raw.depth_slash`, `MuNuMirror` 8/0); (b) `∂𝒜²=0` = the `q=±1` sign-cancel
  (`dsq_zero_universal_delta4` 5/0, `cup1_antisymmetric` 14/0); (c) the homology residue and HF≅singular
  empty/nonzero cases (`reduced_betti_d4_contractible` 11/0, `betti_one_cycle`/`cycle_vs_contractible_qpm`
  56/0); (d) the Arnold/Euler equality (`simplex_face_euler_zero` 10/0); (e) the critical-point =
  periodic-orbit/flat-connection conserved sector (`density_conserved_of_det_one`/`noether_local` 14/0,
  `det_holonomy_eq_one`/`first_loop_is_the_fold` 26/0); (f) the gradient-residue at both poles
  (`gradient_descent_monotone` 9/0, `flow_reaches` 19/0, `no_surjection_of_fixedpointfree` 11/0,
  `self_covering_closure` 7/0, `residue_tag_two_poles` 55/0).
- *Conceptual-only / the precise missing legs (the `morse_theory.md`/`symplectic_geometry.md` shape):*
  **the named `Floer`/`FloerComplex`/`Arnold`/`Maslov`/`ConleyZehnder`/`JHolomorphic`/`ASD`/
  `periodicOrbit`/`flatConnection` objects are ABSENT** (grep-confirmed: zero hits). So the gap is
  exactly the `morse_theory.md` gap one level deeper: (i) an action functional `𝒜 : LM → ℝ` /
  `CS : 𝒜_conn → ℝ` with a critical-point (orbit/connection) set and a CZ-index function; (ii) the
  Floer differential `∂𝒜` assembled from J-holomorphic-cylinder / ASD-instanton counts; (iii) the
  comparison theorem `HF_* ≅ H_*^sing` welded to `reduced_betti_d4_contractible`. The *engine* (the
  gradient diagonal `GradientFlow`/`OneDiagonal`), the *grade* (`Raw.depth`/`Cochain n k`), the
  *differential law* (`dsq_zero`), the *residue* (`ker/im`), the *Euler fold* (`simplex_face_euler_zero`),
  and the *conserved-orbit sector* (`NoetherCurrent`/`det_holonomy_eq_one`) are each built and PURE; only
  the named graded `𝒜`-complex bundle is open.
- *The genuine `Real213`/analytic BREAK — the ∞-dim moduli of J-holomorphic curves.* This is the new,
  deeper break past `morse_theory.md`'s smooth-`f`/Hessian gap. Floer theory's hard content is
  *analytic*: the moduli space `ℳ(x,y)` of J-holomorphic cylinders connecting two orbits is a
  Banach-manifold / Fredholm-operator construction (transversality via Sard–Smale, Gromov compactness,
  gluing) — an infinite-dimensional analytic apparatus that lives entirely in the `Real213`-cut /
  completed-Banach-space corner the calculus reaches by *none* (the same corner as the missing
  continuous integral operator in `differential_equations.md` and the smooth Hessian in
  `morse_theory.md`). The *count* `#ℳ(x,y)` (a finite ℤ) is the residue-machine operand; the *moduli
  space whose count it is* is the analytic break. This is the honest edge: the residue machine is
  built and PURE, the ∞-dim curve-counting apparatus that *feeds* it is the located analytic gap.

So: **PREDICTION on the named object + the deepest CONSOLIDATION in the homology cluster — all five legs
are prior ∅-axiom theorems reused verbatim; the named graded `Floer`/`Arnold`/`Maslov` bundle and the
∞-dim J-holomorphic moduli are the open legs, not a hand-wave.**

## Revelation (consolidation: Floer homology = Morse theory on an ∞-dim functional, no new primitive)

**Collapse — Floer homology is `morse_theory.md`'s residue machine RE-DOMAINED onto the action
functional, not a new theory.** The single fold-height reading on `C`, plus an *infinite-dimensional*
functional `𝒜`/`CS` selecting the grading, *generates the whole field*:
- the **CZ/Maslov index** = `dimension.md`'s height grade `L↑` (`Raw.depth`), read at `𝒜`'s flat spots
  (relative, since the absolute index is infinite — the finite-signature rule) — `morse_theory.md`'s
  Morse index lifted;
- the **Floer differential `∂𝒜`** = `homology.md`'s `∂` (`delta` read DOWN), the J-holomorphic/ASD flow
  count carrying the `(−1)` orientation sign — `∂𝒜²=0` IS `dsq_zero_universal_delta4`;
- **Floer homology ≅ singular homology** = `morse_theory.md`'s "two complexes built from one `C` measure
  ONE residue `Residue(L↓,C)`" (`reduced_betti_d4_contractible`);
- the **Arnold conjecture** = HF≅singular (two readings, one residue) + the Morse weak inequality
  `c_i ≥ b_i` (count ≥ residue dimension) — *the same two ingredients as the Morse inequalities*;
- **critical points = periodic orbits / flat connections** = `symplectic_geometry.md`'s q+1 conserved
  sector (`noether_local`/`det_holonomy_eq_one`), and as a residue the `q=±1` tag of the gradient
  reading — minimizing orbit = `q=+1` converge (`GradientFlow`/`flow_reaches`), extra orbits = `q=−1`
  escape (`no_surjection_of_fixedpointfree` — a non-trivial cycle *forces* an orbit).

This is the literal capstone of `morse_theory.md`'s and `symplectic_geometry.md`'s last lines:
`morse_theory.md` made the residue machine height-graded by `f`; `symplectic_geometry.md` fused the q=−1
antisymmetric bracket with the q=+1 det=1 conservation on phase space. Floer homology is **both at
once** — `morse_theory.md`'s machine run on `symplectic_geometry.md`'s conserved-orbit object,
height-graded by the symplectic action. The infinite-dimensionality is absorbed by the finite-signature
rule: the calculus reads the *relative* index and the *count* `#ℳ(x,y)`, both finite, never the infinite
absolute index or the ∞-dim moduli space itself.

**Residue-surfaced — "periodic orbit" and "flat connection" are the gradient-reading's `q=±1` tag fused
with the conserved sector, not new objects.** A periodic Hamiltonian orbit stops being a primitive of
symplectic topology and becomes (i) where `∇𝒜_H` self-points and vanishes (the gradient residue) AND
(ii) `symplectic_geometry.md`'s conserved flow `{H,H}=0` (`noether_local`). A flat connection is the
same on Chern–Simons: where `∇CS=0` AND `F_A=0` = `det_holonomy_eq_one`. Read with a converge weight it
is the action-minimizer (a fixed point reached, `GradientFlow`); read with an escape weight it is an
extra forced orbit (`OneDiagonal`). Same tag as φ/Cantor/Gödel/curvature/Lefschetz/Morse, now carrying a
CZ-index weight on an ∞-dim functional.

**EXTEND by consolidation; no new axis.** The interior model v7.1 holds: Floer homology is the
fold-height axis (the CZ index grade) × the homology residue (Invariant B, `q=±1`) × the alternating
Euler sum (`L(id)=χ`, the `(−1)^i` orientation bit) × the gradient diagonal (`OneDiagonal`/`GradientFlow`)
× `symplectic_geometry.md`'s conserved-orbit sector — read across {fold-height (the relative index),
direction (the orientation/flow-line sign)}, with the *resolution dial* run all the way to an ∞-dim
domain. The two genuine absences — the named graded `Floer`/`Arnold`/`Maslov` bundle, and the ∞-dim
J-holomorphic moduli (the analytic `Real213`/Banach break) — are located precisely: every leg PURE, the
named graded object and the curve-counting apparatus open.

## Note for the technique

- **Floer homology is the sharpest confirmation that the residue machine is domain-agnostic — it does
  not care whether the functional lives on a finite cell complex or an infinite-dimensional loop space.**
  `morse_theory.md` earned the claim "Morse theory = read-a-space-by-a-height-function". Floer homology
  swaps the height function for the symplectic-action / Chern–Simons functional on an *infinite*-dim
  configuration space, and **every consequence is unchanged**: index = `Raw.depth`, `∂²=0` =
  `dsq_zero`, HF=singular = the two-readings-one-residue, Arnold = HF=singular + the weak inequality.
  The infinite-dimensionality is fully absorbed by the **finite-signature rule** (`README`'s modulus):
  the calculus reads the *relative* CZ index (finite) and the *count* `#ℳ(x,y)` (finite ℤ), never the
  infinite absolute index or the ∞-dim moduli. This is the cleanest possible vindication that the
  residue machine is the field-independent core — Floer = Morse with the domain dialed to ∞.

- **The Floer differential reveals the J-holomorphic cylinder / ASD instanton IS a gradient flow line —
  the same `∂` read-off as `morse_theory.md`, on a harder count.** `morse_theory.md` found `∂f` counts
  gradient lines; Floer's `∂𝒜` counts J-holomorphic cylinders (= gradient trajectories of `𝒜` for the
  `L²`-metric induced by `J`) / ASD instantons (= gradient trajectories of `CS`). That these are the
  same `q=±1`-graded operator (`dsq_zero` again) shows the calculus's `∂` is read-agnostic across
  *three* down-step realizations: a face-removal (simplicial), a finite-dim gradient line (Morse), and a
  J-holomorphic cylinder / ASD instanton (Floer). The *hardness* migrates entirely into constructing the
  count (transversality, Gromov compactness, gluing); the algebraic identity it lands on is `dsq_zero`,
  unchanged.

- **The two parent files meet here for the first time.** `morse_theory.md` (the height-graded residue
  machine) and `symplectic_geometry.md` (the conserved-orbit phase object) were independent
  consolidations. Floer homology is the field where they are **one construction**: the residue machine of
  the first, run on the conserved objects of the second, height-graded by the symplectic action. The
  q=+1/q=−1 fusion `symplectic_geometry.md` found on ω (antisymmetric reading whose flow preserves det=1)
  reappears as the Floer critical-point's two poles (minimizing orbit = q+1, extra forced orbit = q−1) —
  the same two-pole-on-one-object pattern.

- **The break is `differential_equations.md`'s analytic break, not `knots.md`'s quotient break.** Floer
  homology hits NO topological-quotient break (no isotopy, no ambient identification — the comparison
  `HF≅H^sing` is a residue-equality, not a quotient). Its genuine absence is the **∞-dim J-holomorphic /
  ASD moduli** — a Banach-manifold / Fredholm analytic apparatus in the `Real213`-cut corner shared with
  `differential_equations.md`'s continuous integral operator and `morse_theory.md`/`curvature.md`'s
  smooth Hessian/metric. The *count* `#ℳ` is the operand; the *moduli space* is the reached-by-none
  completion. A `Real213`-cut residue, the deepest the geometry cluster has located, not a 213-primitive
  miss.

---

### Verified Lean anchors (file:line:theorem — all grep-confirmed on `lean/E213`; purity via `tools/scan_axioms.py`, run from repo root this session)

| Leg | Theorem (file : line : name) | Status |
|---|---|---|
| ★ **CZ/Maslov index = fold-height grade** (`Raw.depth`, forced by the well-founded build measure) | `Theory/Raw/Lambek.lean:199 : isPart_wf`; `Theory/Raw/Levels.lean:46 : Raw.depth_slash` (`1+max`) | ∅-axiom ✓ (`isPart_wf` is `WellFounded`) |
| ★ **`∂𝒜² = 0`** = the `q=±1` orientation sign-cancel, SAME theorem as `∂²=0` | `Lib/Math/Cohomology/Delta/V4Capstone.lean:41 : dsq_zero_universal_delta4`; `:62 : leibniz_universal_delta4` | **PURE, scanned 5/0** ✓ |
| the J-holo/ASD flow-line `(−1)` sign = the orientation bit (order-swap flips sign) | `Lib/Math/Cohomology/Cup/SignedCup.lean:57 : cup1`; `:62 : cup1_antisymmetric` | **PURE, scanned 14/0** ✓ |
| ★ **Floer homology = `ker∂𝒜/im∂𝒜` = `Residue(L↓,C)`** (HF≅singular, the empty/contractible case) | `Lib/Math/Cohomology/Examples/BettiKernel.lean:63 : reduced_betti_d4_contractible`, `:42 : kerSizeDelta`, `:47 : kerSize_5_0`, `:52 : kerSize_5_1` | **PURE, scanned 11/0** ✓ |
| the nonzero residue (an orbit survives in HF): cycle `q=−1` vs contractible `q=+1` | `Lib/Math/Cohomology/Examples/NonzeroBetti.lean:111 : betti_one_cycle`, `:134 : loopClass_not_coboundary`, `:143 : nonzero_cohomology_class`, `:173 : cycle_vs_contractible_qpm` | **PURE, scanned 56/0** ✓ |
| ★ **Arnold/Euler equality `Σ(−1)^i c_i = χ = Σ(−1)^i b_i`** = `morse_theory.md`'s `L(id)=χ` | `Lib/Physics/Simplex/FaceTerms.lean:125 : simplex_face_euler_zero`; `:85 : simplex_face_counts` | **PURE, scanned 10/0** ✓ |
| ★ **crit pt of 𝒜 = periodic orbit** = `symplectic_geometry.md`'s q+1 conserved flow (`{H,H}=0`, det=1 ⟹ volume preserved) | `Lib/Math/NumberSystems/Real213/ModularGeometry/NoetherCurrent.lean:117 : density_conserved_of_det_one`; `:149 : noether_local` | **PURE, scanned 14/0** ✓ |
| ★ **crit pt of CS = flat connection** = `det=1` around every loop (`F_A=0`) | `Lib/Math/NumberSystems/Real213/ModularGeometry/HolonomyLattice.lean:108 : holonomy_append`; `:136 : det_holonomy_eq_one`; `:313 : first_loop_is_the_fold` | **PURE, scanned 26/0** ✓ |
| ★ **crit pt = gradient residue, `q=+1` converge** (`ẋ=−∇𝒜` reaches a fixed point) | `Lib/Math/Analysis/Optimization/GradientFlow.lean:128 : gradient_descent_identity`; `:138 : gradient_descent_monotone` | **PURE, scanned 9/0** ✓ |
| the FLOW archetype reaching a normal form (action flow reaches a critical orbit) | `Lib/Math/Foundations/MonovariantFlow.lean:99 : flow_reaches`; `:149 : descent_reaches` | **PURE, scanned 19/0** ✓ |
| ★ **crit pt = gradient residue, `q=−1` escape** (a non-trivial cycle forces an orbit — the diagonal can't be dodged) | `Lens/Foundations/OneDiagonal.lean:51 : no_surjection_of_fixedpointfree`; `Lens/Foundations/FlatOntologyClosure.lean:61 : object1_not_surjective`, `:69 : self_covering_closure` | **PURE, scanned 11/0 + 7/0** ✓ |
| the `q=±1` residue tag (minimizing orbit = converge, extra orbit = escape) | `Lib/Math/Foundations/ResidueTag.lean:228 : residue_tag_two_poles`, `:133 : escape_residue_outside`, `:160 : converge_residue_fixed`, `:180 : golden_is_converge`, `:86 : multiplier_unimodular` | **PURE, scanned 55/0** ✓ |
| cross-frame | `morse_theory.md` (Morse machine: index=`Raw.depth`, `∂f`=`L↓`, `∂f²=0`, HM=singular, the weak inequality), `symplectic_geometry.md` (the q+1 conserved orbit, `noether_local`/`det_holonomy_eq_one`), `homology.md`/`de_rham.md` (`∂`=`L↓`, two readings one residue), `gauge_theory.md` (instanton/ASD = flat-connection side, being decomposed in parallel) | prior, ∅-axiom ✓ |

**Scan tallies (this session, `tools/scan_axioms.py E213.<module>` from repo root):** `V4Capstone`
**5/0**; `BettiKernel` **11/0**; `NonzeroBetti` **56/0**; `FaceTerms` **10/0**; `NoetherCurrent`
**14/0**; `HolonomyLattice` **26/0**; `GradientFlow` **9/0**; `MonovariantFlow` **19/0**; `OneDiagonal`
**11/0**; `FlatOntologyClosure` **7/0**; `SignedCup` **14/0**; `ResidueTag` **55/0**. All PURE, 0 DIRTY.

### Dropped / flagged (predicted-not-built — honest, grep-confirmed absent)

- **No named Floer-theory object in `lean/E213`.** Grep (`Floer|Arnold|Conley|Maslov|JHolomorphic|
  J_holomorphic|action_functional|instanton|ASD|pseudoholomorphic`, and
  `Zehnder|periodic_orbit|flat_connection|flatConnection`): **zero hits**. No `FloerComplex`, no
  `floerDifferential`, no `ArnoldConjecture`, no `maslovIndex`/`conleyZehnder`, no `JHolomorphic`/
  `ASDConnection`/`instanton` object, no `periodicOrbit`/`flatConnection` type. Flagged
  predicted-not-built, exactly as `morse_theory.md`/`symplectic_geometry.md` flag their absent named
  objects.
- **No action functional `𝒜 : LM → ℝ` / `CS` with a critical-orbit set and a CZ-index function, no Floer
  differential `∂𝒜` from J-holomorphic/ASD counts, no comparison theorem `HF_* ≅ H_*^sing`.** The
  homology groups exist (`Cochain`, `delta`, `kerSizeDelta`, Betti) but graded by *cell dimension*, not
  by an action index; the conserved-orbit sector exists (`NoetherCurrent`/`det_holonomy_eq_one`) but as a
  finite `Mat2`/lattice object, not a loop-space/connection-space critical set; there is no
  J-holomorphic-cylinder / ASD-instanton moduli count assembling `∂𝒜`. This is the precise missing leg —
  the ∞-dim twin of `morse_theory.md`'s missing graded `Morse`/`MorseComplex` bundle.
- **★ The genuine `Real213`/analytic BREAK — the ∞-dim moduli `ℳ(x,y)` of J-holomorphic curves / ASD
  instantons.** Floer theory's hard analytic content (Banach-manifold moduli, Fredholm index = relative
  CZ index, Sard–Smale transversality, Gromov compactness, gluing) lives in the `Real213`-cut / completed
  -Banach corner the calculus reaches by *none* — the same corner as `differential_equations.md`'s
  continuous integral operator and `morse_theory.md`/`curvature.md`'s smooth Hessian/metric. The *count*
  `#ℳ(x,y)` (a finite ℤ) is the residue-machine operand and is the only thing the discrete machine needs;
  the *moduli space whose count it is* is the located analytic break — deeper than `morse_theory.md`'s
  finite-dim gradient lines, because the configuration space (loop space / connection space) is itself
  infinite-dimensional. Not a 213-primitive miss; the reached-by-none completion the geometry cluster
  shares.

### Named buildable witness (for the orchestrator)

**The Arnold/Morse weak inequality `c_i ≥ b_i` on Δ⁴ (the orbit-count ≥ Betti-number bound), stated at
the dimension level** — identical to `morse_theory.md`'s proposed witness, because Arnold = HF=singular +
this same inequality. ⚠ The naive count form `kerSizeDelta 5 k ≤ binom 5 k` is **FALSE** for `k≥2`
(`kerSizeDelta 5 2 = 16 > binom 5 2 = 10`): `kerSizeDelta` is the cocycle *cardinality* `2^(dim ker δ_k)`,
an exponential, while `binom 5 k` is the cell count `c_k`. The faithful statement is `b_i ≤ dim ker δ_i ≤
c_i`, whose count form `kerSizeDelta 5 k ≤ 2^(binom 5 k)` is TRUE (`16 ≤ 2^10` at `k=2`) but `decide`
overflows the `2^10` filter — it needs the structural `ker δ_k ⊆ Cᵏ ⟹ |ker| ≤ |Cᵏ|` argument or the
`log₂`-dimension extraction, not a one-line `decide`. The Arnold/Euler *equality* `Σ(−1)^i c_i = χ`
(count form, clean `decide`) is already in hand (`simplex_face_euler_zero` 10/0). Both sides' *data* are
PURE (`BettiKernel` 11/0, `NonzeroBetti` 56/0, `FaceTerms` 10/0); the missing piece is the dimension
extraction, shared verbatim with `morse_theory.md`. No new witness is asserted beyond this; the named
graded `Floer`/`Arnold` bundle and the ∞-dim J-holomorphic moduli remain the open legs.
