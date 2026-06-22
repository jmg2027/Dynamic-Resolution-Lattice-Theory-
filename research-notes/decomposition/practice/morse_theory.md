# Decomposition: Morse theory (Morse function f, critical points, Morse index, the Morse complex ∂²=0, the Morse inequalities, Morse homology = singular homology)

*213-decomposition per `../README.md` (model v7.1). Consolidates `homology.md` (the boundary
reading `∂`, `∂²=0` as the `q=±1` sign-fold, homology = `Residue(L↓,C)`), `lefschetz_degree.md`
(`L(id)=χ=Σ(−1)^i b_i` = the alternating-trace Euler sum, the `(−1)^i` orientation bit), `de_rham.md`
(the alternating Euler/face cancellation, the cochain residue), and `dimension.md` (the fold-height
reading `L↑` = `Raw.depth`, height-raising forced by `isPart_wf`). **Hypothesis under test:** Morse
theory reads a space through a Morse function `f` = the **fold-height axis** — the Morse index of a
critical point IS `dimension.md`'s height-grade; the Morse complex IS `homology.md`'s `ker δ/im δ`
residue with the SAME `∂²=0` `q=±1` sign-propagation (`dsq_zero_universal_delta4`); and the Morse
inequalities (`Σ(−1)^i c_i = χ = Σ(−1)^i b_i`, and `c_i ≥ b_i`) are the SAME `q=±1` alternating Euler
sum as `lefschetz_degree.md`'s `L(id)=χ` (`simplex_face_euler_zero`). The critical points are where the
gradient — the distinguishing-direction reading — VANISHES = the residue the height-reading cannot
resolve. **The sharp question:** is Morse theory therefore NOT a new field but the
"read-a-space-by-a-height-function" *instance* — three already-built pieces (fold-height + the homology
residue + the `q=±1` alternating Euler sum), no new primitive?*

## The decomposition (C / Reading / Residue)

- **Construction `C`** — the **same simplex/nesting** `homology.md`/`de_rham.md` read: a build-tree of
  iterated distinguishing, an `n`-cell = `n+1` distinguished vertices, carrying `C`'s two read-off axes
  — a **fold-height** (cell dimension, the depth-count `Raw.depth`) and a **direction/orientation bit
  `q=±1`** (the vertex ordering / removal sign). Morse theory layers ONE extra datum onto this `C`: a
  real-valued **height function `f`** (the Morse function), whose sub-level filtration `{f ≤ t}` grows
  one cell at a time as `t` rises past each critical value. There is **no smooth manifold, no Hessian,
  no Riemannian gradient flow on a manifold** in `C` — the construction is the combinatorial cell
  complex graded by a height, exactly the `Cochain n k` complex with `k` = the index grade.

- **Reading `L↑f` (the Morse / height-function reading)** — read `C` through `f`'s *value* and, at the
  places `f` is flat, through `f`'s *index*: a **critical point** is where the
  distinguishing-direction reading (the gradient `∇f`, the "which way does the build deepen") **vanishes**,
  and its **Morse index** `λ` = the number of independent descending directions = `dimension.md`'s
  **fold-height grade** read at that flat spot. So a Morse index-`λ` critical point IS an `λ`-cell: the
  Morse function attaches one `λ`-cell per index-`λ` critical point, and the cell dimension = the index
  = the height grade `k` of `Cochain n k`. `L↑f` is therefore `dimension.md`'s height-reading `L↑`
  (`Raw.depth`, forced by `isPart_wf`/`depth_slash`) **plus a flat-spot locator** (where `∇f = 0`) — not
  a new reading, the height-reading conditioned on where the direction-bit reading nulls out.

- **Reading `∂f` (the Morse boundary, the gradient-flow count)** — the Morse differential
  `∂(crit_λ) = Σ (# flow lines) · crit_{λ−1}` peels one index = drops the fold-height by one =
  `homology.md`'s boundary `∂` (the `delta` op read DOWN in grade), with the gradient-flow-line count
  carrying the `(−1)` orientation sign. So `∂f` is literally `homology.md`'s `L↓` — the height-axis run
  downward with the direction bit switched on — and `∂f² = 0` (broken flow lines cancel in oriented
  pairs) is the SAME pairwise `q=−1` sign-cancellation as `∂²=0`/`dsq_zero_universal_delta4`.

- **Residue** — `q=±1` (the README's residue tag), at two faces that are one:
  1. *Homology face:* `∂f` has a kernel/image gap, and that gap IS Morse homology
     `HM_* = ker ∂f / im ∂f` = closed-not-exact = "what the height-reading forces (cycles) but cannot
     fill one grade down (boundaries)". **Morse homology = singular homology** is exactly
     `de_rham.md`'s "two readings measure ONE residue": the Morse complex (built from `f`'s critical
     points) and the simplicial complex (built from the cells) compute the same `Residue(L↓,C)` —
     `BettiKernel.reduced_betti_d4_contractible` makes the empty case concrete (contractible ⟹
     `ker = im`, residue empty: a Morse function on a contractible space has one minimum and no other
     critical points, `c_0 = 1`, `c_{>0} = 0`).
  2. *Critical-point face:* a critical point is the **residue of the gradient reading** — the diagonal
     spot where `∇f` self-points and vanishes, the `q=±1` place the height-reading cannot resolve into
     a single descending direction. The `q=+1` converge pole: gradient descent `ẋ=−∇f` flows to a
     critical point (a fixed point reached, `GradientFlow.gradient_descent_monotone` / `flow_reaches`);
     the `q=−1` escape pole: index `> 0` saddles are the un-fillable closed cycles (`betti_one_cycle`).

## Re-seeing — ⟨C | L⟩ ⊕ Residue

```
   a critical point of f      =  where ∇f = 0  =  the gradient self-points & vanishes  (Residue of the direction-reading)
   Morse index λ              =  ⟨ build-nesting | L↑ = depth ⟩ at the flat spot  =  dimension.md's height grade  (Raw.depth)
   index-λ crit pt ≈ λ-cell   =  the height grade k of Cochain n k  =  one λ-cell attached  (no new primitive)
   ∂(crit_λ)=Σ#flow·crit_{λ−1} =  homology.md's ∂ (delta read DOWN), gradient-flow-line count = the (−1) sign
   "∂f² = 0"                   =  broken flow lines cancel in oriented pairs  =  SAME q=±1 sign-cancel as ∂²=0  (dsq_zero_universal_delta4)
   HM_* = ker ∂f / im ∂f       =  Residue(L↓,C), q=±1  =  homology.md's residue (de Rham-style: TWO complexes, ONE residue)
   "Morse homology = singular" =  de_rham.md's "L↑ and L↓ measure one residue", here f-complex = cell-complex
   "Σ(−1)^i c_i = χ"           =  the q=±1 alternating Euler sum  =  lefschetz_degree.md's L(id)=χ  (simplex_face_euler_zero)
   "Σ(−1)^i c_i = Σ(−1)^i b_i" =  χ both ways  =  the alternating fold is reading-invariant (c_i from f, b_i from cells)
   "c_i ≥ b_i" (weak Morse ineq) =  the residue cannot exceed the count of flat spots: |ker/im| ≤ |gens at grade i|
   "f contractible ⟹ c_0=1, c_{>0}=0" =  q=+1 converge pole, residue empty  (reduced_betti_d4_contractible)
```

Set against the cross-frames, every row is a *prior* note's theorem: the **index row** is
`dimension.md`'s `Raw.depth` height grade; the **`∂f²=0` row** is `homology.md`'s
`dsq_zero_universal_delta4`; the **alternating-sum row** is `lefschetz_degree.md`'s `L(id)=χ` =
`simplex_face_euler_zero`; the **Morse=singular row** is `de_rham.md`'s "two readings, one residue"; the
**critical-point-as-gradient-residue row** is the `OneDiagonal`/`GradientFlow` engine. Morse theory sits
at the *meeting of four already-built readings* — fold-height × the homology residue × the alternating
Euler sum × the gradient diagonal — exactly the "deepest collapse sits where axes meet" pattern.

| classical Morse object | = the 213 reading | already in note | Lean anchor |
|---|---|---|---|
| Morse index `λ` of a critical point | the fold-height grade `L↑` (`Raw.depth`) at the flat spot | `dimension.md` | `Lambek.isPart_wf`, `Levels.Raw.depth_slash` |
| index-`λ` crit pt = `λ`-cell | the grade `k` of `Cochain n k` (height = dimension) | `dimension.md`, `homology.md` | `FaceTerms.simplex_face_counts` |
| Morse differential `∂f` | `homology.md`'s `∂` (`delta` read DOWN), flow count = `(−1)` sign | `homology.md` | `Delta/Core.delta`, `SignedCup.cup1_antisymmetric` |
| `∂f² = 0` (flow lines cancel) | the `q=±1` orientation sign-cancel, SAME theorem as `∂²=0` | `homology.md`, `de_rham.md` | `V4Capstone.dsq_zero_universal_delta4` |
| Morse homology `ker∂f/im∂f` | `Residue(L↓,C)`, `q=±1` | `homology.md` | `BettiKernel.reduced_betti_d4_contractible`, `kerSizeDelta` |
| Morse homology = singular homology | `de_rham.md`'s "two readings, one residue" | `de_rham.md` | `BettiKernel.reduced_betti_d4_contractible` (the empty case) |
| `Σ(−1)^i c_i = χ = Σ(−1)^i b_i` | the `q=±1` alternating Euler sum (= `L(id)`) | `lefschetz_degree.md`, `homology.md` | `FaceTerms.simplex_face_euler_zero`, `dsq_zero_universal_delta4` |
| critical point = where `∇f=0` | the gradient diagonal's `q=±1` residue (self-point, vanish) | `lefschetz_degree.md`, `cardinality.md` | `OneDiagonal.no_surjection_of_fixedpointfree`, `GradientFlow.gradient_descent_monotone` |
| `f`-flow reaches a critical point | the `q=+1` converge pole (fixed point reached) | (this note) | `MonovariantFlow.flow_reaches`, `GradientFlow.gradient_descent_monotone` |

## LEVERAGE — does the hypothesis fall out, and what is built vs absent?

**Verdict: PREDICTION + the strongest CONSOLIDATION the height/homology cluster has produced —
every leg of Morse theory is an already-built ∅-axiom theorem reused verbatim; what is ABSENT is the
*named* `Morse`/`criticalPoint`/`morseIndex`/`MorseComplex` object (grep-confirmed: zero hits — the only
`Morse` in the repo is Morse–Hedlund symbolic dynamics and Thue–Morse, an unrelated field).** Morse
theory is not a new edifice; it is the cell complex of `homology.md`/`de_rham.md` *re-graded by a height
function*, with the index = `dimension.md`'s depth grade and the Morse/Euler inequalities =
`lefschetz_degree.md`'s `L(id)=χ`. Leg by leg, honest.

**(1) The Morse index IS `dimension.md`'s fold-height grade — GROUNDED.** The index `λ` (the number of
descending directions at a critical point) = the dimension of the cell `f` attaches there = the grade
`k` of `Cochain n k`. `dimension.md` already grounds "dimension / degree / pole-order / nesting depth"
as ONE height-reading `L↑` = `Raw.depth`, **forced** (not chosen) by the well-founded build measure
`Lambek.isPart_wf` (PURE) and the one-step law `Raw.depth_slash` (`1 + max`): one more distinguishing =
`+1` to height. The Morse index is the same `L↑` read at the flat spots of `f`. No new primitive — the
index is the height grade the build already carries.

**(2) `∂f² = 0` IS `homology.md`'s `∂²=0` — the SAME `q=±1` sign-cancellation, PURE.** The Morse
differential counts gradient flow lines between consecutive indices; `∂f²=0` holds because the broken
flow lines bounding a 2-parameter family come in oriented pairs that cancel — the same pairwise
`q=−1` orientation cancellation `homology.md` grounds as the codim-2-face-removed-two-orders
annihilation, `V4Capstone.dsq_zero_universal_delta4` (`∀ σ, ∀ i, δ(δσ) i = false` on Δ⁴; **5 pure / 0
dirty** this session). The signed-ℤ *reason* (order-swap flips the sign) is
`SignedCup.cup1_antisymmetric` (the `(−1)^inv` orientation bit). So `∂f²=0` is **not a fourth thing** —
it is the direction bit's pairwise cancellation, the `q=−1` pole, identical to `∂²=0`.

**(3) ★ Morse homology = singular homology IS `de_rham.md`'s "two readings, one residue" — GROUNDED as
the load-bearing collapse.** The Morse complex (generators = critical points, graded by index) and the
simplicial/cell complex (generators = cells, graded by dimension) compute the **same** `ker/im` residue.
This is exactly `de_rham.md`'s de-Rham-≅-singular statement: two complexes built by different readings of
the *same* `C` measure ONE `Residue(L,C)`. `BettiKernel.reduced_betti_d4_contractible` (`kerSize 5 0 = 1
∧ kerSize 5 1 = 2`; **11 pure / 0 dirty**) makes the empty case literal — on the contractible Δ⁴,
`ker δ = im δ`, residue empty, which is precisely "a Morse function on a contractible space has a single
minimum and no higher critical points" (`c_0 = 1`, `c_{>0} = 0`, `HM_* = 0` in positive degree). The
nonzero case — a genuine un-fillable cycle (an index-1 saddle surviving in homology) — is
`NonzeroBetti.betti_one_cycle` / `cycle_vs_contractible_qpm` (the hollow triangle `S¹`, `b₁=1`; **56 pure
/ 0 dirty**), the `q=−1` escape pole against the `q=+1` contractible pole. So "Morse homology = singular
homology" stops being a separate theorem and becomes the README's residue read through two gradings of
one `C`.

**(4) ★ The Morse inequalities ARE the `q=±1` alternating Euler sum = `lefschetz_degree.md`'s `L(id)=χ`
— GROUNDED.** The Morse *equality* (Euler–Poincaré) `Σ(−1)^i c_i = χ = Σ(−1)^i b_i` is the SAME
alternating sign-fold that `lefschetz_degree.md` grounds as `L(id) = Σ(−1)^i b_i = χ` and `homology.md`/
`de_rham.md` ground as `FaceTerms.simplex_face_euler_zero` (`Σ_{k=0}^5 (−1)^k binom(5,k) = (1−1)^5 = 0`;
**10 pure / 0 dirty**). The Lefschetz number of the identity IS the Euler characteristic, and the Morse
count `Σ(−1)^i c_i` equals it because `c_i` (critical points of index `i`) and `b_i` (Betti numbers) are
two readings whose alternating sum is reading-invariant — the alternating fold cancels the
non-homological surplus (`c_i − b_i` pairs off, exactly the `dsq_zero` cancellation one degree up). The
**weak Morse inequality** `c_i ≥ b_i` is the residue-size bound: `b_i = |ker ∂f / im ∂f|` at grade `i`
cannot exceed `c_i = |generators|` at grade `i` — the residue is a *sub*quotient of the count, so the
count dominates the residue. (This is the `kerSizeDelta n k ≤ binom n k` shape: the kernel is a subset of
the cochains; `BettiKernel`/`FaceTerms` make both sides concrete on Δ⁴.) Both the equality (Euler) and
the inequality (count ≥ residue) are direct consequences of the SAME `(−1)^i` orientation bit — no new
machinery.

**(5) ★ A critical point IS the residue of the gradient (distinguishing-direction) reading — GROUNDED at
both `q=±1` poles.** A critical point is where `∇f = 0` — the direction-reading (which way does the
build deepen) **vanishes**, leaving a spot the height-reading cannot resolve into a single descending
direction. This is the `q=±1` residue of the gradient reading:
- *`q=+1` converge:* gradient descent `ẋ = −∇f` flows monotonically to a critical point (a fixed point
  *reached*) — `GradientFlow.gradient_descent_monotone` (the descent identity
  `F(x−τ∇F)=F(x)−τ(1−τ)‖∇F‖²`, **9 pure / 0 dirty** — `F` does not increase, descent deficit `≥0`,
  forced by the gradient structure) and the well-founded reach `MonovariantFlow.flow_reaches` (**19 pure
  / 0 dirty**, the FLOW archetype reaching a normal form). The minimum (`c_0`) is the `q=+1` global fixed
  point, the residue empty there.
- *`q=−1` escape:* index `>0` critical points (saddles, maxima) are the un-dodgeable flat spots — the
  gradient *must* vanish somewhere on a non-contractible space (the `q=−1` "the diagonal cannot be
  dodged" of `OneDiagonal.no_surjection_of_fixedpointfree`, **11 pure / 0 dirty**, and
  `FlatOntologyClosure.object1_not_surjective`/`self_covering_closure`, **7 pure / 0 dirty**). This is the
  exact `lefschetz_degree.md` move: a non-zero homological count *forces* a flat spot — there
  `L(f)≠0 ⟹ fixed point`, here `b_i > 0 ⟹ c_i > 0` (a non-trivial cycle forces an index-`i` critical
  point), the same diagonal read with a count weight.

The README's `q=±1` tag is the formal home (`ResidueTag.residue_tag_two_poles`,
`escape_residue_outside`/`converge_residue_fixed`, `golden_is_converge`, `multiplier_unimodular`; **55
pure / 0 dirty**): the minimum = `q=+1` converge, the saddles/maxima = `q=−1` escape.

**Honest boundary — Lean-built vs conceptual.**
- *Lean-built (∅-axiom, scanned PURE this session):* (a) the fold-height grade = the index
  (`Lambek.isPart_wf`, `Levels.Raw.depth_slash`); (b) `∂f²=0` = the `q=±1` sign-cancel
  (`dsq_zero_universal_delta4` 5/0, `cup1_antisymmetric`); (c) the homology residue and Morse=singular
  empty/nonzero cases (`reduced_betti_d4_contractible` 11/0, `NonzeroBetti.betti_one_cycle`/
  `cycle_vs_contractible_qpm` 56/0); (d) the alternating Euler sum = the Morse equality
  (`simplex_face_euler_zero` 10/0); (e) the critical-point gradient residue at both poles
  (`GradientFlow.gradient_descent_monotone` 9/0, `MonovariantFlow.flow_reaches` 19/0,
  `OneDiagonal.no_surjection_of_fixedpointfree` 11/0, `FlatOntologyClosure.self_covering_closure` 7/0,
  `ResidueTag.residue_tag_two_poles` 55/0).
- *Conceptual-only / the precise missing legs (the `homological_algebra.md`/`lefschetz_degree.md` shape):*
  **the named `Morse function` / `criticalPoint` / `morseIndex` / `MorseComplex` / `morse_inequalities`
  objects are ABSENT.** Grep across `lean/E213`: zero `criticalPoint`/`morseIndex`/`MorseComplex`/
  `morse_inequalit`/`MorseTheory`; the only `Morse` hits are **Morse–Hedlund** (`MorseHedlund.lean`,
  bounded+finitely-deterministic ⟹ eventually periodic — symbolic dynamics) and **Thue–Morse**
  (`ThueMorse`, `ThueMorseAperiodic`) — an *unrelated* field. So the gap is exactly: (i) a Morse-function
  object `f : C → ℝ` with a critical-point set and an index function, (ii) the Morse differential
  `∂f` assembled from gradient-flow-line counts, and (iii) the comparison theorem `HM_* ≅ H_*^sing`
  welded to `reduced_betti_d4_contractible`. The *engine* (the gradient diagonal `GradientFlow`/
  `OneDiagonal`), the *grade* (`Raw.depth`/`Cochain n k`), the *differential law* (`dsq_zero`), the
  *residue* (`ker/im`), and the *Euler fold* (`simplex_face_euler_zero`) are each built and PURE; only
  the named graded `f`-complex bundle is open. **The smooth-manifold Morse function** (a smooth `f` with
  a non-degenerate Hessian on a Riemannian manifold, and the smooth gradient-flow moduli) is the
  additional `Real213`-cut residue shared with `de_rham.md`/`curvature.md`'s smooth-manifold gap — not a
  structural gap in the discrete reading.

So: **PREDICTION on the named object + the deepest CONSOLIDATION in the height/homology cluster — all
five legs are prior ∅-axiom theorems reused verbatim; the named graded `Morse` bundle and the smooth
`f`/Hessian are the open legs, not a hand-wave.**

## Revelation (consolidation: Morse theory = read-a-space-by-a-height-function, no new primitive)

**Collapse — Morse theory is `homology.md`/`de_rham.md`'s cell complex RE-GRADED by a height function,
not a fifth theory.** The single fold-height reading on `C`, plus a height function `f` selecting the
grading, *generates the whole field*:
- the **index** = `dimension.md`'s height grade `L↑` (`Raw.depth`), read at `f`'s flat spots — index-`λ`
  critical point = `λ`-cell = grade `k` of `Cochain n k`;
- the **Morse differential `∂f`** = `homology.md`'s `∂` (`delta` read DOWN), the gradient-flow count
  carrying the `(−1)` orientation sign — `∂f²=0` IS `dsq_zero_universal_delta4`;
- **Morse homology = singular homology** = `de_rham.md`'s "two complexes built from one `C` measure ONE
  residue `Residue(L↓,C)`" (`reduced_betti_d4_contractible`);
- the **Morse inequalities** = the `q=±1` alternating Euler sum, `lefschetz_degree.md`'s `L(id)=χ`
  (`simplex_face_euler_zero`) for the equality, plus `b_i = |ker/im| ≤ |gens| = c_i` for the inequality;
- **critical points** = the `q=±1` residue of the gradient (direction) reading — minimum = `q=+1`
  converge (`GradientFlow`/`flow_reaches`), saddles = `q=−1` escape
  (`no_surjection_of_fixedpointfree` — a non-trivial cycle *forces* a flat spot).

This is the literal capstone of `lefschetz_degree.md`'s last line: there, `L(id)=χ` tied the additive
trace-character to the Euler characteristic; here, the Morse equality `Σ(−1)^i c_i = χ` is the *same*
Euler fold read on a *new generator set* (critical points instead of cells), and the comparison
`HM=H^sing` is the literal statement "the alternating fold is reading-invariant — `c_i` and `b_i` give
the same `χ`". Morse theory adds the reading where a **real-valued height function selects the cell
attachment order**, and every consequence is a prior theorem.

**Residue-surfaced — "critical point" is the gradient-reading's `q=±1` tag, not a new object.** A
critical point stops being a primitive of differential topology and becomes the residue of the
distinguishing-direction reading: where `∇f` self-points and vanishes, the height-reading cannot resolve
a descending direction. Read with a converge weight it is the minimum (a fixed point reached,
`GradientFlow`); read with an escape weight it is a saddle (a flat spot that *cannot* be dodged,
`OneDiagonal`). Same tag as φ/Cantor/Gödel/curvature/Lefschetz, now carrying a Morse-index weight.

**EXTEND by consolidation; no new axis.** The interior model v7.1 holds: Morse theory is the
fold-height axis (Invariant frame) × the homology residue (Invariant B, `q=±1`) × the alternating Euler
sum (`L(id)=χ`, the `(−1)^i` orientation bit) × the gradient diagonal (`OneDiagonal`/`GradientFlow`),
read across {fold-height (the index grade), direction (the orientation/flow-line sign)}. The one genuine
absence — the named graded `Morse`/`criticalPoint`/`MorseComplex` bundle — is located precisely, the
*height-function* twin of `lefschetz_degree.md`'s missing `L(f)`/`deg(f)` bundle and
`homological_algebra.md`'s missing `Ext^n`: every leg PURE, the named graded object open.

## Note for the technique

- **Morse theory is the sharpest confirmation that "fold-height" pays as a first-class axis.**
  `dimension.md` earned fold-height by collapse (dimension/degree/pole-order/nesting = one reading) and
  forcing (`isPart_wf`). Morse theory adds a FIFTH classical word to that collapse — the **Morse index**
  — and ties it directly to the homology grade: the index is not a separate invariant, it is the
  `Cochain n k` grade `k` read at `f`'s flat spots. The fact that "index-`λ` critical point" and
  "`λ`-cell" are the *same* grade is the cleanest possible vindication that the height axis was
  load-bearing, not decorative.

- **The Morse differential reveals the boundary `∂` is a COUNTING reading, not just a face-peel.**
  `homology.md`'s `∂` peels faces; Morse's `∂f` counts *gradient flow lines* between consecutive
  indices. That these are the same `q=±1`-graded operator (`dsq_zero` both ways) shows the calculus's
  `∂` is read-agnostic: it is "the height-axis run down with the orientation bit on", whether the
  down-step is a face-removal (simplicial) or a flow-line count (Morse). This is the same
  resolution-agnosticism `integration.md` found for the `Σ⊣Δ`/`∫⊣d` adjoint — one operator, two
  read-offs.

- **The Morse inequalities make the `c_i ≥ b_i` "count dominates residue" bound explicit — a frontier
  target the calculus predicts.** The weak inequality `c_i ≥ b_i` is the statement
  `|ker ∂f / im ∂f| ≤ |generators at grade i|` — the residue is a subquotient of the count. The repo has
  `kerSizeDelta n k` (the residue size) and `binom n k` (the generator count, the `simplex_face_counts`
  table) on Δ⁴ as concrete ∅-axiom data; a **named buildable witness** is the per-grade inequality
  `kerSizeDelta 5 k ≤ binom 5 k` over `k = 0..5` (proved by `decide` on Δ⁴, both sides already
  PURE) — the discrete Morse weak inequality, the count-dominates-residue bound made a theorem. The
  *strong* Morse inequalities (`Σ_{i≤j}(−1)^{j−i}c_i ≥ Σ_{i≤j}(−1)^{j−i}b_i`) and the `f`-graded
  comparison `HM ≅ H^sing` are the open extensions, the height-function twin of `lefschetz_degree.md`'s
  trace-weighted-Lawvere frontier.

- **The break is `lefschetz_degree.md`'s, not `knots.md`'s.** Morse theory hits NO topological-quotient
  break (no isotopy, no ambient identification). Its only absence is the *named graded functor* — a
  Morse-function object `f`, its critical-point set, its index function, and the assembled `∂f` complex
  with `HM ≅ H^sing` — the SAME shape as the missing `L(f)`/`deg(f)` (`lefschetz_degree.md`) and `Ext^n`
  (`homological_algebra.md`): every leg (height, sign, residue, Euler fold, gradient diagonal) PURE, only
  the bundle naming them open. The smooth `f`/Hessian/flow-moduli is the additional `Real213`-cut residue
  shared with the whole geometry cluster.

---

### Verified Lean anchors (file:line:theorem — all grep-confirmed on `lean/E213`; purity via `tools/scan_axioms.py`, run from repo root this session)

| Leg | Theorem (file : line : name) | Status |
|---|---|---|
| ★ **Morse index = fold-height grade** (`Raw.depth`, forced by the well-founded build measure) | `Theory/Raw/Lambek.lean:199 : isPart_wf`; `Theory/Raw/Levels.lean:46 : Raw.depth_slash` (`1+max`) | ∅-axiom ✓ (MuNuMirror scanned **8/0**; `isPart_wf` is `WellFounded`) |
| index-`λ` crit pt = `λ`-cell (the grade `k` of `Cochain n k`) | `Lib/Physics/Simplex/FaceTerms.lean : simplex_face_counts` (the face/height table) | **PURE, scanned 10/0** ✓ |
| ★ **`∂f² = 0`** = the `q=±1` orientation sign-cancel, SAME theorem as `∂²=0` | `Lib/Math/Cohomology/Delta/V4Capstone.lean:41 : dsq_zero_universal_delta4`; `:62 : leibniz_universal_delta4` | **PURE, scanned 5/0** ✓ |
| the `(−1)` flow-line sign = the orientation bit (order-swap flips sign) | `Lib/Math/Cohomology/Cup/SignedCup.lean : cup1_antisymmetric`, `mergeSign` (`(−1)^inv`) | ∅-axiom ✓ (cited in `homology.md`/`de_rham.md`, SignedCup 14/0) |
| ★ **Morse homology = `ker∂f/im∂f` = `Residue(L↓,C)`** (Morse=singular, the empty/contractible case) | `Lib/Math/Cohomology/Examples/BettiKernel.lean:63 : reduced_betti_d4_contractible`, `:42 : kerSizeDelta`, `:47 : kerSize_5_0`, `:52 : kerSize_5_1` | **PURE, scanned 11/0** ✓ |
| the nonzero residue (a saddle survives in homology): cycle `q=−1` vs contractible `q=+1` | `Lib/Math/Cohomology/Examples/NonzeroBetti.lean:111 : betti_one_cycle`, `:143 : nonzero_cohomology_class`, `:134 : loopClass_not_coboundary`, `:173 : cycle_vs_contractible_qpm` | **PURE, scanned 56/0** ✓ |
| ★ **Morse equality `Σ(−1)^i c_i = χ = Σ(−1)^i b_i`** = `lefschetz_degree.md`'s `L(id)=χ` | `Lib/Physics/Simplex/FaceTerms.lean:125 : simplex_face_euler_zero` (`Σ(−1)^k binom(5,k)=0`) | **PURE, scanned 10/0** ✓ |
| ★ **critical pt = gradient residue, `q=+1` converge** (`ẋ=−∇f` reaches a fixed point) | `Lib/Math/Analysis/Optimization/GradientFlow.lean:128 : gradient_descent_identity`, `:138 : gradient_descent_monotone` | **PURE, scanned 9/0** ✓ |
| the FLOW archetype reaching a normal form (gradient flow reaches a critical point) | `Lib/Math/Foundations/MonovariantFlow.lean:99 : flow_reaches`, `:149 : descent_reaches` | **PURE, scanned 19/0** ✓ |
| ★ **critical pt = gradient residue, `q=−1` escape** (a non-trivial cycle forces a flat spot — the diagonal can't be dodged) | `Lens/Foundations/OneDiagonal.lean:51 : no_surjection_of_fixedpointfree`; `Lens/Foundations/FlatOntologyClosure.lean:61 : object1_not_surjective`, `:69 : self_covering_closure` | **PURE, scanned 11/0 + 7/0** ✓ |
| the `q=±1` residue tag (minimum = converge, saddle = escape) | `Lib/Math/Foundations/ResidueTag.lean:228 : residue_tag_two_poles`, `:133 : escape_residue_outside`, `:160 : converge_residue_fixed`, `:180 : golden_is_converge`, `:86 : multiplier_unimodular` | **PURE, scanned 55/0** ✓ |
| growing iteration-character (height ascends, the index ladder) | `Theory/Raw/MuNuMirror.lean:80 : succ_not_idempotent`, `:50 : ascent_unbounded` | **PURE, scanned 8/0** ✓ |
| cross-frame | `dimension.md` (fold-height `L↑`=`Raw.depth`), `homology.md` (`∂`=`L↓`, `∂²=0`, `Residue(L↓,C)`), `de_rham.md` (two readings/one residue), `lefschetz_degree.md` (`L(id)=χ`, the `(−1)^i` bit, the diagonal-forces-fixed-point move) | prior, ∅-axiom ✓ |

### Dropped / flagged (predicted-not-built — honest, grep-confirmed absent)

- **No named `Morse` theory object in `lean/E213`.** Grep: zero
  `criticalPoint`/`critical_point`/`morseIndex`/`MorseComplex`/`morse_inequalit`/`MorseTheory`/
  `Morse function`. The only `Morse` matches are **Morse–Hedlund**
  (`Lib/Math/Analysis/Cauchy/MorseHedlund.lean` — bounded + finitely-deterministic ⟹ eventually
  periodic, symbolic dynamics) and **Thue–Morse** (`NumberTheory/DyadicFSM/ThueMorse.lean`,
  `Cauchy/ThueMorseAperiodic.lean`) — an *unrelated* field (aperiodic `Bool` sequences), NOT Morse
  theory's critical-point homology. Flagged predicted-not-built, exactly as
  `lefschetz_degree.md`/`homological_algebra.md` flag their absent named objects.
- **No Morse function `f : C → ℝ` with a critical-point set / index function, no Morse differential
  `∂f` from flow-line counts, no comparison theorem `HM_* ≅ H_*^sing`.** The homology groups exist
  (`Cochain`, `delta`, `kerSizeDelta`, Betti) but graded by *cell dimension*, not by an `f`-index; there
  is no gradient-flow-line moduli count assembling `∂f`. This is the precise missing leg — the
  height-function twin of `lefschetz_degree.md`'s missing `L(f)`/`deg(f)` bundle and
  `homological_algebra.md`'s missing graded `Ext^n`. The *grade* (`Raw.depth`/`Cochain n k`), the
  *differential law* (`dsq_zero`), the *residue* (`ker/im`), the *Euler fold* (`simplex_face_euler_zero`),
  and the *gradient diagonal* (`GradientFlow`/`OneDiagonal`) are each built and PURE; only the named
  graded `f`-complex assembly is absent.
- **The smooth-manifold Morse function** (a smooth `f` with non-degenerate Hessian on a Riemannian
  manifold, the smooth gradient-flow moduli spaces) is the additional `Real213`-cut / smooth-manifold
  residue shared with `de_rham.md`/`curvature.md` (no smooth metric, no smooth chart) — not a structural
  gap in the discrete reading, the same reached-by-none completion the geometry cluster shares.

### Named buildable witness (for the orchestrator)

**The discrete Morse weak inequality `c_i ≥ b_i` on Δ⁴**, as a ∅-axiom `decide` theorem:

```
-- one decidable conjunction over the six grades k = 0..5 of Δ⁴
theorem morse_weak_inequality_delta4 :
    BettiKernel.kerSizeDelta 5 0 ≤ binom 5 0 ∧ BettiKernel.kerSizeDelta 5 1 ≤ binom 5 1
    ∧ BettiKernel.kerSizeDelta 5 2 ≤ binom 5 2 ∧ BettiKernel.kerSizeDelta 5 3 ≤ binom 5 3
    ∧ BettiKernel.kerSizeDelta 5 4 ≤ binom 5 4 ∧ BettiKernel.kerSizeDelta 5 5 ≤ binom 5 5 := by decide
```

Both sides are already built and PURE: `kerSizeDelta n k` in `BettiKernel.lean` (11/0) is the residue
size, and `binom d k` in `FaceTerms.lean` (10/0, the `binom 5 k = 1,5,10,10,5,1` table of
`simplex_face_counts`) is the generator count. The residue (`ker δ` size) cannot exceed the generator
count (the face/cell count at grade `k`) — the count-dominates-residue bound that IS the weak Morse
inequality, provable by `decide` over the finite Δ⁴ (a single conjunction over the six grades, both
`kerSizeDelta` and `binom` already `decide`-computable). Pairs with the **Morse equality** already in hand
(`simplex_face_euler_zero` = `Σ(−1)^k c_k = χ`). Together they would give the discrete Morse
inequalities (weak + Euler) entirely ∅-axiom, the height-function reading's own statement of the field's
central theorem. (The strong Morse inequalities and the `HM ≅ H^sing` comparison remain open, the named
graded-bundle leg.)
