# Decomposition: the Lefschetz fixed-point theorem + Brouwer degree

*213-decomposition per `../README.md` (model v7.1). Consolidates `homology.md` (the boundary
reading `∂`, `∂²=0` as the `q=±1` sign-fold, homology = `Residue(L↓,C)`), `determinant.md` (the
`×↦·` character, `det=±1` orientation bit), `de_rham.md` (the alternating Euler/face cancellation,
the cochain residue), and — load-bearing — `fundamental_group.md` (the loop-holonomy reading, the
`q=−1` first non-contractible loop) and `cardinality.md`/the `OneDiagonal` engine (the
fixed-point-free diagonal). **Hypothesis under test:** the **Lefschetz number**
`L(f) = Σ_i (−1)^i tr(f_* | H^i)` is the calculus's **character arrow** (`tr` = the additive `×↦+`
trace-readout, the `tr=e₁` Vieta object) **alternating-summed down the fold-height** (the `(−1)^i`
is `homology.md`'s `q=±1` orientation bit, the SAME `∂²=0`/Euler sign-propagation); and the theorem
`L(f) ≠ 0 ⟹ f has a fixed point` IS the `q=±1` diagonal — a fixed point is where `f` meets the
diagonal `Δ`, the SAME diagonal `no_surjection_of_fixedpointfree` / `object1_not_surjective` run on.
**Brouwer degree** `deg(f)` = the character read on the *top* homology `H^n` (a single ℤ-valued
multiplicative readout = the holonomy/`det` character); no-retraction / hairy-ball = the `q=−1`
escape (the diagonal cannot be dodged). The sharp question: **is Lefschetz the *graded,
trace-weighted* version of the Lawvere fixed-point engine — so that "fixed-point theorem" and "the
residue's non-closure" are one `(C,L)` object, read with a trace weight?***

## The decomposition (C / Reading / Residue)

- **Construction `C`** — TWO constructions that meet at the diagonal:
  1. the **simplex / chain complex** `homology.md` reads (an `n`-cell = `n+1` distinguished
     vertices, the build-tree of iterated distinguishing), carrying `C`'s two read-off axes — a
     **fold-height** (the cell/degree `i`) and a **direction/orientation bit `q=±1`** (the vertex
     ordering / removal sign);
  2. a **self-map** `f : C → C` of that construction, read against the **diagonal** `Δ = {(x,x)}` —
     a self-pointing of the construction, the SAME shape `Object1 : Raw → (Raw → Bool)` /
     `f : A → A → B` carries in `OneDiagonal.lean`. A **fixed point** of `f` is a point of `f ∩ Δ`.
     `C` here is `fundamental_group.md`'s/`curvature.md`'s loop-carrying transition-history read as a
     self-endomorphism.

- **Reading `L_χ↓` (the graded trace-character, alternating-summed down the height)** — read the
  induced map `f_*` on each homology group `H^i` to a **trace** (`Mat2.tr`, the additive `×↦+`
  twin of `det`: `tr M = M.a + M.d = e₁ = Σλ`), then **alternate-sum down the fold-height** with the
  `(−1)^i` orientation bit: `L(f) = Σ_i (−1)^i tr(f_* | H^i)`. This composes two readings the
  calculus already isolates: (a) `representation.md`/`spectral.md`'s **trace** = the `×↦+` character
  `tr=e₁` (`tr_eq_e1`), the *additive* twin of `determinant.md`'s `×↦·` `det=e₂`; and (b)
  `homology.md`'s **alternating-sign down the height** = the `(−1)^i` Euler/`∂²=0` orientation
  cancellation (`simplex_face_euler_zero`: `Σ(−1)^k binom = 0`). So `L_χ↓` is *not a new reading*: it
  is the trace-character (Invariant A, additive mode) run **down the bidirectional fold-height** with
  the `q=±1` direction bit — exactly `de_rham.md`'s "one character read down the height", but
  weighted by `tr` instead of evaluated as `det`.

- **Reading `L_deg` (Brouwer degree, the top-homology character)** — the *single* `ℤ`-valued
  multiplicative readout of `f_*` on the **top** homology `H^n` of an `n`-sphere: `deg(f) ∈ ℤ`,
  with `deg(f∘g) = deg(f)·deg(g)`. This is `L_χ↓` restricted to one degree and read
  *multiplicatively* — i.e. **`determinant.md`'s `×↦·` character / `det_holonomy_eq_one`'s holonomy
  winding** (`det(MN)=det M·det N`, `holonomy_append`): degree = winding number = the holonomy `det`
  character on the loop `H^n`. `deg=±1` is `parity.md`'s/`determinant.md`'s orientation bit; general
  `deg` is the same character opened to all of ℤ.

- **Residue** — `q=±1` (the README's residue tag), the *same* diagonal at its two signs:
  - **`q=−1` escape:** when `f` is **fixed-point-free** (`f ∩ Δ = ∅`), the diagonal cannot be
    pointed by `f` — `no_surjection_of_fixedpointfree` / `object1_not_surjective` fire. Lefschetz's
    contrapositive `L(f) ≠ 0 ⟹ fixed point` says: a *non-zero* graded-trace forces `f` to meet `Δ`;
    equivalently `f` fixed-point-free ⟹ `L(f) = 0`. Brouwer's no-retraction / hairy-ball / "no
    fixed-point-free map of the even sphere" is *exactly* the `q=−1` "the diagonal cannot be dodged".
  - **`q=+1` converge:** when `f` is a contraction / the construction is contractible, the fixed
    point *exists and is reached* — `banach_fixed_point_modulated` / `converge_residue_fixed`,
    `homology.md`'s `reduced_betti_d4_contractible` (contractible ⟹ residue empty, every map has the
    forced fixed point: `L(f) = 1` for any self-map of a contractible space).

## Re-seeing — ⟨C | L⟩ ⊕ Residue

```
   a fixed point of f       =  a point of f ∩ Δ  =  f self-pointing the construction  (Object1/Lawvere shape)
   L(f) = Σ(−1)^i tr(f_*|Hⁱ) =  ⟨ chain complex + self-map | L_χ↓ = trace-character down the height, q=±1 weighted ⟩
   the trace tr(f_*|Hⁱ)      =  the ×↦+ character e₁ = Σλ                    (Mat2Spectrum.tr_eq_e1)
   the alternating (−1)^i     =  homology.md's q=±1 orientation bit          (simplex_face_euler_zero, dsq_zero)
   "L(f) ≠ 0 ⟹ fixed point"  =  Lawvere contrapositive: t fixed-point-free ⟹ no surjection of the self-cover
                              =  no_surjection_of_fixedpointfree   (the diagonal cannot be dodged)
   "f contractible ⟹ L(f)=1, has a fixed point"  =  q=+1 converge pole  (banach / reduced_betti contractible)
   deg(f) (Brouwer)           =  ⟨ top homology Hⁿ | L_deg = the ×↦· holonomy/det character ⟩
   "deg(f∘g)=deg(f)·deg(g)"   =  the ×↦· character                          (det2_mul / holonomy_append)
   "deg = winding"            =  the holonomy det of the loop                (det_holonomy_eq_one neighborhood)
   no retraction / hairy ball =  q=−1 escape: no fixed-point-free map of Sⁿ  (no_surjection_of_fixedpointfree)
```

Set against the cross-frames — the **trace row is `representation.md`/`spectral.md`'s `tr=e₁`**
verbatim, the **alternating-sign row is `homology.md`/`de_rham.md`'s `(−1)^i` Euler/`∂²=0` bit**, the
**degree-multiplicativity row is `determinant.md`/holonomy's `×↦·` character**, and the **fixed-point
row is the `OneDiagonal` Lawvere engine** — Lefschetz/Brouwer sit at the *meeting of three already-built
readings* (trace-character × fold-height × diagonal), exactly the "deepest collapse sits where axes
meet" pattern.

| classical object | = the 213 reading | already in note | Lean anchor |
|---|---|---|---|
| trace `tr(f_*\|H^i)` | the `×↦+` character `tr=e₁=Σλ` | `representation.md`, `spectral.md` | `Mat2Spectrum.tr_eq_e1` |
| the `(−1)^i` alternating sum | `homology.md`'s `q=±1` orientation / Euler cancel | `homology.md`, `de_rham.md` | `simplex_face_euler_zero`, `dsq_zero_universal_delta4` |
| `L(f)≠0 ⟹ fixed point` | Lawvere contrapositive (diagonal can't be dodged) | `cardinality.md`, the residue | `no_surjection_of_fixedpointfree` |
| contractible ⟹ `L=1`, fixed pt | `q=+1` converge pole (residue empty) | `homology.md` | `reduced_betti_d4_contractible`, `banach_fixed_point_modulated` |
| `deg(f∘g)=deg f·deg g` | the `×↦·` holonomy/`det` character | `determinant.md`, `fundamental_group.md` | `det2_mul`, `holonomy_append`, `det_holonomy_eq_one` |
| no retraction / hairy ball | `q=−1` escape (no fixed-point-free self-map) | `cardinality.md`, `godel.md` | `no_surjection_of_fixedpointfree` |

## LEVERAGE — does the hypothesis fall out, and what is built vs absent?

**Verdict: PREDICTION + PARTIAL — three of the four legs are GROUNDED in built ∅-axiom Lean (the
trace `×↦+` character, the alternating `q=±1` Euler/`∂²=0` cancellation, the fixed-point/diagonal
engine), and the degree-multiplicativity = the `×↦·` holonomy character; what is ABSENT is the
*named* `Lefschetz`/`degree`/`fixedPointTheorem` object and the *graded `f_*` action on `H^i`* — there
is no `L(f) = Σ(−1)^i tr(f_*)` def, no `brouwerDegree`, no induced-map-on-homology in the repo.** Leg
by leg, honest.

**(1) The trace is the `×↦+` character `tr=e₁` — GROUNDED, but as a NON-multiplicative readout.**
`Mat2.tr M = M.a + M.d` (`HyperbolicEllipticTrace.lean:47`) is exactly `spectral.md`'s `tr=e₁=Σλ`
(`Mat2Spectrum.tr_eq_e1`, 9/0 PURE: `tr M = μ+ν` when `M` factors `(λ−μ)(λ−ν)`), the **additive twin**
of `determinant.md`'s `det=e₂=Πλ`. The crucial honest point `representation.md` already pinned: `tr`
is **not** a character-*homomorphism* — there is no `tr(MN)=tr M·tr N` (and there can be none). So the
Lefschetz number's *summands* are the additive `×↦+` readout, and the alternating sum (leg 2) is what
makes the *whole* `L(f)` carry the fixed-point information — `L(f)` is a graded trace, the `×↦+`
character read down the height, not a multiplicative character. The trace recurrence
`tr(M^{n+2})=tr M·tr(M^{n+1})−det M·tr(M^n)` (`Mat2TraceRecurrence.trace_recurrence`, 5/0 PURE) shows
the *iterated* trace is governed by Cayley–Hamilton — the same `tr·M − det·I` Vieta object, so even
"trace of a power of a self-map" is a built recurrence (`golden_trace_recurrence`: the Lucas
sequence is `tr(G^n)`, φ's iterator). This is the precise sense the trace-character is built.

**(2) The alternating `(−1)^i` IS `homology.md`'s `q=±1` orientation bit — GROUNDED, the same
theorem.** Lefschetz's `(−1)^i` and Brouwer-via-Euler-characteristic's `χ = Σ(−1)^i b_i` are the
**same alternating sign** `de_rham.md`/`homology.md` ground as `simplex_face_euler_zero`
(`FaceTerms.lean:125`, 10/0 PURE: `Σ_{k=0}^{5}(−1)^k binom(5,k) = (1−1)^5 = 0`) and the `∂²=0`
two-step cancellation `dsq_zero_universal_delta4` (`V4Capstone.lean:41`, 5/0 PURE). The Lefschetz
number of the *identity* map is exactly `Σ(−1)^i b_i = χ` (the Euler characteristic), so
**`L(id) = χ` is `simplex_face_euler_zero`'s alternating Betti sum** — on the contractible Δ⁴ it is
`(1−1)^5 = 0`-type vanishing of the *reduced* sum, with `χ = 1` for the full simplex
(`reduced_betti_d4_contractible`, `BettiKernel.lean:63`, 11/0 PURE: `b̃₀=b̃₁=0`). The `(−1)^i` is the
direction bit `q=±1`, the *same* sign that flips `det`, gives ℤ's `−`, and makes `∂²=0` cancel
pairwise. No new primitive — the orientation axis was already bidirectional.

**(3) ★ `L(f) ≠ 0 ⟹ fixed point` IS the Lawvere/diagonal engine — GROUNDED as the deepest collapse
here.** This is the load-bearing claim and it lands cleanly. A fixed point of `f` is a point of
`f ∩ Δ` — `f` *self-pointing* the construction, the **exact shape** of `OneDiagonal.lean`'s
`f : A → A → B` and `Object1 : Raw → (Raw → Bool)`. The contrapositive form of Lefschetz —
"`f` fixed-point-free ⟹ `L(f) = 0`", equivalently "`L(f) ≠ 0` forces `f` to meet `Δ`" — is the
SAME logical move as `no_surjection_of_fixedpointfree` (`OneDiagonal.lean:51`, 11/0 PURE): *if* a
modifier `t : B → B` is fixed-point-free *then* the self-cover leaves a residue (cannot point the
diagonal). Lefschetz is the **graded, trace-weighted refinement**: instead of the raw Bool/Prop
diagonal `g a := t(f a a)`, Lefschetz weights the diagonal intersection `f ∩ Δ` by the local
trace/index and sums it `Σ(−1)^i tr` — the trace IS the *intersection number* of `f` with `Δ`, the
quantitative version of `lawvere_fixed_point`'s qualitative "a fixed point exists". So:
**`lawvere_fixed_point` / `no_surjection_of_fixedpointfree` = the Lefschetz engine read with a Bool
weight; `L(f)` = the same engine read with a `tr=e₁` weight down the height.** "Fixed-point theorem"
and "the residue's non-closure" (Cantor/Gödel/`object1_not_surjective`) are ONE `(C,L)` object — the
self-cover/diagonal — read with two different weights. This is the central revelation and it is
fully grounded in `OneDiagonal`/`FlatOntologyClosure` (both PURE).

**(4) Brouwer degree = the `×↦·` holonomy/`det` character on top homology; no-retraction/hairy-ball =
the `q=−1` escape — GROUNDED as readings, the named `deg` object ABSENT.** `deg(f∘g)=deg f·deg g`
is the multiplicative `×↦·` character `determinant.md` grounds as `det2_mul` and
`fundamental_group.md`/`curvature.md` ground as the holonomy winding `holonomy_append` /
`det_holonomy_eq_one` (`HolonomyLattice.lean:108,136`, 26/0 PURE — `det` of a loop = the winding/flat
invariant). `deg = winding = holonomy det` is the same `×↦·` arrow `fundamental_group.md` reads around
a loop: `first_loop_is_the_fold` (`:313`, `holonomy[S,S] = −I ≠ I`) is the `q=−1` non-trivial winding,
`positive_loop_trivial` (`:292`) the `q=+1` flat sector. Brouwer's "no fixed-point-free self-map of
`S^{2n}`" / hairy-ball is the `q=−1` escape `no_surjection_of_fixedpointfree` again — the diagonal
cannot be dodged on the even sphere because `L(f) = 1 + (−1)^{2n}deg(f) ≠ 0` forces a fixed point.
**ABSENT:** there is no `brouwerDegree`/`degree`/`winding_number` def, and no induced action of a
self-map on the homology groups `H^i` — so the *summands* `tr(f_*|H^i)` are not assembled into an
`L(f)` def. The pieces (trace, alternating sign, holonomy det, the diagonal) are all built and PURE;
the *named graded object* assembling them is not.

**Honest boundary — Lean-built vs conceptual.**
- *Lean-built (∅-axiom, scanned PURE this session):* (a) the trace `×↦+` character `tr=e₁`
  (`Mat2Spectrum`, 9/0) + the iterated-trace recurrence (`Mat2TraceRecurrence`, 5/0); (b) the
  alternating `(−1)^i` Euler/`∂²=0` cancellation (`FaceTerms.simplex_face_euler_zero` 10/0,
  `V4Capstone.dsq_zero_universal_delta4` 5/0); (c) the fixed-point/diagonal engine
  (`OneDiagonal.no_surjection_of_fixedpointfree`/`lawvere_fixed_point` 11/0,
  `FlatOntologyClosure.object1_not_surjective`/`self_covering_closure` 7/0); (d) the `q=+1` converge
  pole (`reduced_betti_d4_contractible` 11/0, `banach_fixed_point_modulated`,
  `ResidueTag.converge_residue_fixed`/`residue_tag_two_poles` 55/0) and the `q=−1` escape
  (`ResidueTag.escape_residue_outside`, `NonzeroBetti.cycle_vs_contractible_qpm` 56/0); (e) the
  degree `×↦·` holonomy character (`HolonomyLattice.det_holonomy_eq_one`/`holonomy_append` 26/0,
  `first_loop_is_the_fold`).
- *Conceptual-only / the precise missing legs:* **the named `Lefschetz`/`degree` objects are ABSENT.**
  Grep across `lean/E213`: zero `lefschetz_number`/`Lefschetz` (the only `Lefschetz` hits are **Hard
  Lefschetz** / **Lefschetz (1,1)** in the Hodge-theory cluster — a *different* theorem,
  `AbelianSurfaceHodge.lefschetz_one_one_t4`, about `(1,1)`-classes, NOT the fixed-point theorem);
  zero `brouwerDegree`/`mapping_degree`/`winding_number`/`no_retraction`/`hairy`; the only `Brouwer`
  hits are **Brouwerian bar-induction** (`WKLHeineBorel`, constructive logic) — NOT Brouwer's
  fixed-point theorem. And there is **no induced action of a self-map `f` on the homology groups
  `H^i`** — the summands `tr(f_*|H^i)` cannot be formed. So the gap is exactly: (i) the
  homology-functoriality `f_* : H^i → H^i` and (ii) the assembly `L(f) = Σ(−1)^i tr(f_*)` /
  `deg(f) = tr(f_*|H^n)` as a named def, with the theorem `L(f)≠0 ⟹ ∃ fixed point` welded to
  `lawvere_fixed_point`. The *engine* (the diagonal), the *weight* (`tr=e₁`), and the *grading*
  (`(−1)^i`) are each built and PURE; only the named graded bundle is open — exactly the
  `homological_algebra.md`/`de_rham.md` pattern (every leg PURE, the named graded object absent).

So: **PREDICTION on the named object + PARTIAL grounding — the strongest *collapse* is that Lefschetz
is the trace-weighted Lawvere engine (leg 3, fully built), and degree is the `×↦·` holonomy character
(leg 4); the smooth/continuous mapping degree and the named `L(f)`/`deg(f)` bundle are the open legs,
not a hand-wave.**

## Revelation (collapse: Lefschetz = the trace-weighted Lawvere diagonal; degree = the holonomy character)

**Collapse — "fixed-point theorem" and "the residue's non-closure" are ONE `(C,L)` object, read with
two weights.** The single self-cover/diagonal reading — `f` self-pointing the construction, `f ∩ Δ`
— *generates both*: read with a **Bool weight** (`t = not`, fixed-point-free) it is
`cantor_via_lawvere`/`object1_not_surjective` (the `q=−1` escape: Cantor, Gödel, the residue); read
with a **`tr=e₁` weight summed down the fold-height** (`Σ(−1)^i tr(f_*|H^i)`) it is the Lefschetz
number, whose non-vanishing forces the diagonal to be met. This is the deepest collapse the entry
makes: **`no_surjection_of_fixedpointfree` IS the Lefschetz fixed-point theorem at Bool resolution**;
`L(f)` is its trace-graded refinement. The same `OneDiagonal` engine that underlies Cantor/Gödel/Vitali
(SYNTHESIS §3's `q=−1` spine) underlies the *topological* fixed-point theorem — "a fixed point is
unavoidable" and "the diagonal cannot be pointed" are one fact, weighted differently.

**Collapse 2 — the character is read a FIFTH way.** The README's capstone reads the `det`/`×↦·`
character four ways — scalar (`determinant`), `Aut`-invariant (`noether`), around a loop
(`curvature`/holonomy), down the height (`homology`, `∂`). Lefschetz/degree add the reading where the
character is **summed down the height against a self-map** (`L(f) = Σ(−1)^i tr(f_*)`) — the
*additive* `tr=e₁` twin run down the bidirectional fold-height with the `q=±1` orientation bit — and
**degree** is the `×↦·` character on the *top* degree (holonomy winding). So `L(id) = χ` ties the
additive trace-character directly to `homology.md`'s Euler characteristic (`simplex_face_euler_zero`),
and `deg` ties to `fundamental_group.md`'s holonomy winding (`det_holonomy_eq_one`). The det/tr split
(`spectral.md`'s `e₁`/`e₂`) is exactly the **degree/Lefschetz split**: `deg` is the multiplicative
`det`-flavoured top-degree readout, `L(f)` the additive `tr`-flavoured graded readout — the two Vieta
coefficients of the self-map's induced spectrum, summed down the height.

**Residue-surfaced — "has a fixed point" is the `q=±1` tag at the self-map reading.** `f`
contractible / contraction ⟹ `L(f)=1`, the fixed point exists and is *reached* (the `q=+1` converge
pole, `reduced_betti_d4_contractible`/`banach_fixed_point_modulated`); `f` fixed-point-free ⟹ the
diagonal escapes, `L(f)=0`, the residue oscillates outside (`q=−1`,
`no_surjection_of_fixedpointfree`). So "the Lefschetz fixed-point theorem" stops being a separate
object and becomes **the `q=±1` residue tag read at the trace-weighted self-cover** — the same tag
as φ/Cantor/Gödel/curvature, now carrying a `tr` weight.

**EXTEND by consolidation; no new axis.** The interior model v7.1 holds: Lefschetz/Brouwer are the
trace-character (Invariant A, additive mode) × the `q=±1` residue tag (Invariant B) × the diagonal
engine, read across {fold-height (the `(−1)^i` grading), direction (the orientation bit)}. The one
genuine absence — the named graded `f_*`/`L(f)`/`deg(f)` bundle — is located precisely, the
fixed-point twin of `homological_algebra.md`'s missing `Ext^n` object: every leg PURE, the bundle open.

## Note for the technique

- **Lefschetz is the sharpest evidence the diagonal engine is *quantitative*, not just qualitative.**
  `OneDiagonal` proves "a fixed point exists" (or "the self-cover leaves a residue") as a *yes/no*
  fact. Lefschetz says the *signed count* of fixed points is a homological invariant `Σ(−1)^i tr`.
  This suggests a frontier target the calculus predicts: a **trace-weighted `lawvere_fixed_point`** —
  attach to `lawvere_fixed_point`'s witness `f a a` a local index/trace and prove the *count* (not
  just existence) is the alternating trace sum. The Bool engine is built; the `ℤ`-weighted index
  refinement is the open extension, and it would be the calculus's own statement of Lefschetz.

- **The det/tr split (`spectral.md`) recurs AS the degree/Lefschetz split — confirming it is
  structural.** `deg` = the multiplicative `det=e₂` readout on the top degree; `L(f)` = the additive
  `tr=e₁` readout summed down the height. The "opposition" `representation.md` flagged dissolves the
  same way: both are Vieta coefficients of the induced self-map spectrum (`det_tr_split_is_e1_e2`),
  read at one degree (`deg`) vs across all degrees (`L`). No new edge — the same `e₁`/`e₂` Vieta
  object, now indexed by the fold-height.

- **The break is `homological_algebra.md`'s, not `knots.md`'s.** Unlike `fundamental_group.md` (which
  hits the *isotopy-quotient* topological break), Lefschetz/Brouwer's absence is the *named graded
  functor* absence (`f_* : H^i → H^i` and the assembled `L(f)`) — the SAME shape as the missing
  `Ext^n`/`Tor_n` object: every leg (trace, sign, diagonal, holonomy) PURE, only the bundle naming
  them open. The continuous/smooth mapping degree (degree of a smooth `S^n → S^n` map) is the
  additional `Real213`-cut residue shared with `curvature.md`/`de_rham.md`'s smooth-manifold gap.

---

### Verified Lean anchors (file:line:theorem — all grep-confirmed on `lean/E213`; purity via `tools/scan_axioms.py`, run from repo root this session)

| Leg | Theorem (file : line : name) | Status |
|---|---|---|
| ★★ **`L(f)≠0 ⟹ fixed pt` = the Lawvere/diagonal engine** (fixed-point-free ⟹ self-cover leaves residue) | `Lens/Foundations/OneDiagonal.lean:51 : no_surjection_of_fixedpointfree`; `:43 : lawvere_fixed_point`; `:61 : cantor_via_lawvere`; `:101 : one_diagonal_generates` | **PURE, scanned 11/0** ✓ |
| ★ the residue = the non-surjected diagonal (the self-cover faithful, never total) | `Lens/Foundations/FlatOntologyClosure.lean:61 : object1_not_surjective`; `:47 : object1_injective`; `:69 : self_covering_closure` | **PURE, scanned 7/0** ✓ |
| ★ **trace = the `×↦+` character `tr=e₁=Σλ`** (Lefschetz summands; the additive twin of `det=e₂`) | `…/Mat2/Mat2Spectrum.lean:115 : tr_eq_e1`; `:103 : det_eq_e2`; `:204 : det_tr_split_is_e1_e2`; `:167 : disc_eq_gap_squared` | **PURE, scanned 9/0** ✓ |
| `Mat2.tr` def (`tr m = m.a + m.d`); iterated trace = Cayley–Hamilton recurrence (`tr(M^n)` = Lucas) | `…/ModularGeometry/HyperbolicEllipticTrace.lean:47 : tr` (`:45 : det`); `…/Mat2/Mat2TraceRecurrence.lean:53 : trace_recurrence`, `:65 : golden_trace_recurrence`, `:76 : golden_trace_seed` | ∅-axiom ✓ (TraceRecurrence scanned **5/0**) |
| ★ **the alternating `(−1)^i` = `q=±1` orientation bit** (`L(id)=χ=Σ(−1)^i b_i`) | `Lib/Physics/Simplex/FaceTerms.lean:125 : simplex_face_euler_zero` (`Σ(−1)^k binom(5,k)=0`) | **PURE, scanned 10/0** ✓ |
| the `(−1)^i` as `∂²=0` pairwise sign-cancellation (`homology.md`'s mechanism) | `Lib/Math/Cohomology/Delta/V4Capstone.lean:41 : dsq_zero_universal_delta4`; `:62 : leibniz_universal_delta4` | **PURE, scanned 5/0** ✓ |
| ★ **`q=+1` converge pole: contractible ⟹ residue empty ⟹ forced fixed pt** (`L=1`) | `Lib/Math/Cohomology/Examples/BettiKernel.lean:63 : reduced_betti_d4_contractible`, `:42 : kerSizeDelta` | **PURE, scanned 11/0** ✓ |
| `q=−1` escape vs `q=+1` contractible, as a residue witness (nonzero `H¹`) | `Lib/Math/Cohomology/Examples/NonzeroBetti.lean:173 : cycle_vs_contractible_qpm`, `:111 : betti_one_cycle`, `:143 : nonzero_cohomology_class` | **PURE, scanned 56/0** ✓ |
| ★ **degree = the `×↦·` holonomy/`det` character** (`deg(f∘g)=deg f·deg g` = winding) | `…/ModularGeometry/HolonomyLattice.lean:108 : holonomy_append`, `:136 : det_holonomy_eq_one`, `:313 : first_loop_is_the_fold` (`q=−1` winding), `:292 : positive_loop_trivial` (`q=+1`) | **PURE, scanned 26/0** ✓ |
| the residue `q=±1` tag (escape = no-retraction/hairy-ball, converge = contractible fixed pt) | `Lib/Math/Foundations/ResidueTag.lean:228 : residue_tag_two_poles`, `:133 : escape_residue_outside`, `:160 : converge_residue_fixed`, `:86 : multiplier_unimodular`, `:180 : golden_is_converge` | **PURE, scanned 55/0** ✓ |
| cross-frame | `homology.md` (`∂²=0`, Euler sign, `Residue(L↓,C)`), `de_rham.md` (alternating cancel, the cochain residue), `fundamental_group.md` (loop-holonomy, `q=−1` first loop), `determinant.md` (`det=e₂`, `×↦·`), `representation.md`/`spectral.md` (the det/tr=e₁/e₂ split) | prior, ∅-axiom ✓ |

### Dropped / flagged (predicted-not-built — honest, grep-confirmed absent)

- **No named `Lefschetz number` / `lefschetz_fixed_point` object in `lean/E213`.** Grep:
  zero `lefschetz_number`/`L(f)`/`lefschetzNumber`. The only `Lefschetz` matches are **Hard
  Lefschetz** and the **Lefschetz (1,1) theorem** in the Hodge-conjecture cluster
  (`Lib/Math/Cohomology/Surfaces/AbelianSurfaceHodge.lean:230 : lefschetz_one_one_t4`,
  `HodgeRiemann.lean`, `T2Squared.lean`) — a *different* theorem (about which `(1,1)`-cohomology
  classes are algebraic), NOT the topological fixed-point theorem. Flagged predicted-not-built,
  exactly as `surreal.md`/`knots.md` flag their absent named objects.
- **No Brouwer degree / mapping degree / winding-number object.** Grep: zero
  `brouwerDegree`/`mapping_degree`/`topological_degree`/`winding_number`/`no_retraction`/`hairy`.
  The only `Brouwer` matches are **Brouwerian bar-induction / the fan theorem** (`WKLHeineBorel.lean`,
  `HeineCantor.lean`, `Dini.lean`) — constructive *logic*, NOT Brouwer's fixed-point theorem. The
  `degree` matches across the repo are **polynomial / algebraic degree** (`AlgebraicDegree`,
  `DegreeCriterion`, `PolynomialDepth`), not topological mapping degree. Flagged predicted-not-built.
- **No induced action `f_* : H^i → H^i` of a self-map on homology.** The homology groups exist
  (`Cochain`, `delta`, `kerSizeDelta`, Betti numbers) but there is no functorial `f_*` on them, so
  the Lefschetz summands `tr(f_*|H^i)` cannot be assembled. This is the precise missing leg — the
  fixed-point twin of `homological_algebra.md`'s missing graded `Ext^n` bundle. The *engine* (the
  diagonal), the *weight* (`tr=e₁`), and the *grading* (`(−1)^i`) are each built and PURE; only the
  named graded assembly is absent.
- **The continuous/smooth mapping degree** (degree of a smooth `S^n → S^n`) is the additional
  `Real213`-cut / smooth-manifold residue shared with `curvature.md`/`de_rham.md` (no smooth form
  bundle / no smooth chart) — not a structural gap in the discrete reading, the same
  reached-by-none completion the geometry cluster shares.
