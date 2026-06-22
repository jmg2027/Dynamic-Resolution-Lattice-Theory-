# Decomposition: knots / braids (the braid group, knot invariants)

*213-decomposition per `../README.md` (model v6). **Deliberate model-stresser** — knot/braid theory
is far from this repo's content. Hypothesis under test: a braid = a **composition of crossings**, each
crossing a *directed* distinguishing of two strands (over/under = the direction bit `q=±1`); the braid
group `Bₙ` = a composition-closed reading-family (`groups.md`'s `Aut`-family) under the braid
relations; a knot invariant (Jones/Alexander) = a **character** of that family — a
composition-respecting reading into a polynomial ring, like `det`/`sign` but for braids. Test:
does {direction + Aut-family + character} FIT, or does it BREAK?*

**Honest grounding note up front.** There is **no knot or braid theory in `lean/E213/`** — `grep`
for `knot|braid|Jones|skein|Reidemeister` returns: `hknotper` (a "not-period" variable name — false
positive), "two-axis braid" used *metaphorically* for the Möbius probe-twist `(m,k)↦(2m+k,m+k)`, and
**one real structural hit**: `braid relation (ts)³ = e`, the Coxeter presentation of Sym(3)
(`C3ChainCapstone.c3_chain_master` (f)). So this decomposition is grounded **only in structural
analogues** (Sym(n) composition-families, the `q=±1` orientation bit, the `det` character) — the
topological object itself is absent, and that absence is itself one of the findings.

## The decomposition (C / Reading / Residue)

- **Construction `C`** — a **braid word** = `n` distinguished strands, and a *history of crossings*.
  Each generator `σᵢ` distinguishes adjacent strands `i, i+1` by **passing one over the other** —
  this is a distinguishing (which strand is distinct from which neighbour) carrying a **direction
  bit**: over (`σᵢ`) vs under (`σᵢ⁻¹`) is the README's `q=±1` orientation/swap-bit. A braid word is
  `C` built by **composition** `σ_{i₁}^{±1} · σ_{i₂}^{±1} · …` — the README's "readings compose in
  series" applied to crossings. So far this is *exactly* `groups.md`'s shape: a
  distinguishing-structure on `n` positions, with self-readings (the crossings) under composition.

- **Reading `L`** — two stacked readings, mirroring `groups.md`:
  - the **family reading** `Bₙ = Aut`-style closed family of crossing-compositions. The underlying
    *permutation* (forget over/under, keep the swap) is the surjection `Bₙ → Sym(n)` — and *that*
    target is the one piece this repo actually has (`PermGroup`, `mulPerm_comp` Cayley).
  - the **character** `Bₙ → ℤ[t,t⁻¹]` (Jones/Alexander) — a composition-respecting reading into a
    Laurent-polynomial ring, the direct analogue of `det : mul ↦ ·` (`det2_mul`). The polynomial
    *variable* `t` is meant to be the README's direction bit `q` **promoted from `±1` to a formal
    indeterminate** — over/under is no longer just a sign, it is a *graded* sign `t^{±1}`.

- **Residue** — the writhe / linking number is the cheap residue (`Bₙ → ℤ` by signed crossing-count,
  the abelianisation — literally `det`'s sign-count). But the **load-bearing residue is the one the
  calculus cannot reach**: the *isotopy* equivalence. Two different braid words give the *same* knot
  (Markov moves; Reidemeister moves on the diagram). The knot is the residue of the
  word→isotopy-class reading — and unlike every prior residue in this notebook, **it is not generated
  by the reading's own self-application** (no diagonal, no `q=±1` fixed-point asymptote). It is a
  *topological* quotient imposed from a space the calculus has no construction for.

## Re-seeing (⟨C | L⟩)

```
   a braid          =  ⟨ n strands (distinguishing) | the closed family of crossing-compositions ⟩
   crossing σᵢ      =  a DIRECTED distinguishing of strands i,i+1   (over/under = q=±1, README direction bit)
   σᵢ⁻¹             =  the undo-reading (inverse), as in groups.md (composeList_invPerm_left)
   Bₙ → Sym(n)      =  forget the direction bit → the PERMUTATION (the repo's real object: PermGroup)
   braid relation σᵢσ_{i+1}σᵢ = σ_{i+1}σᵢσ_{i+1}  =  the Coxeter relation, repo has (ts)³=e for Sym(3)
   writhe / linking =  signed crossing count  =  Bₙ → ℤ abelianisation  =  det's sign-count (q=±1)
   a knot invariant =  ⟨ Bₙ | character into ℤ[t,t⁻¹] ⟩   (HOPED: det's mul↦· with q promoted to t)
   the knot itself  =  Residue(word → isotopy class) — a TOPOLOGICAL quotient, NOT a self-application residue
```

Set against `groups.md`/`determinant.md`/`homology.md`: the **first two rows fit perfectly** — a
crossing is a directed distinguishing, `Bₙ` is an `Aut`-style composition family, `Bₙ→Sym(n)` is the
calculus's own "forget the direction bit, keep the swap" (the same arrow that takes `det` to
`|det|`). The trouble is concentrated in the **last two rows**.

> **Follow-up (v7.1, `two_cells.md`):** a META-decomposition of natural transformations re-partitioned
> this break into THREE shapes — and one of the two gaps below partly dissolves. The skein relation's
> *algebraic form* (Gap 1) is the calculus's **graded-relation slot**, grounded in-repo by the Leibniz
> rule `leibniz_universal_delta4` (`δ(α⌣β)=δα⌣β ⊕ α⌣δβ`) — distinct from the character arrow (its
> two-term degenerate case), still a real new construct. The isotopy quotient (Gap 2) stands, relocated
> to the un-built colimit/`q=−1` corner + an absent ambient-space construction. (The *naturality* shape
> of "relation among constructions" turned out to be already-built — the 2-cell `view_factors_through_morphism`.)

## Verdict — **EXTEND on the braid group, BREAK on the knot invariant.** Honest split:

The calculus **FITS the braid *group*** cleanly: a crossing is a directed distinguishing (over/under
= `q=±1`), `Bₙ` is exactly `groups.md`'s composition-closed `Aut`-family, and `Bₙ→Sym(n)` is the
"forget the direction bit" arrow the repo already has (`PermGroup`, Cayley `mulPerm_comp`). It
**BREAKS on the knot invariant** at two distinct points the apparatus genuinely lacks: (1) the
**skein relation** `t⁻¹V(L₊) − tV(L₋) = (t^{½}−t^{-½})V(L₀)` is a *three-term linear relation among
different crossings*, not a multiplicative character `V(αβ)=V(α)V(β)` — so a knot invariant is **not
a character in this calculus's sense** (it is not operation-preserving; the Jones polynomial is not a
homomorphism out of `Bₙ`); and (2) the invariant must be constant on the **Markov/Reidemeister
quotient** (an *isotopy* equivalence from a topological space), which is **not** a self-application
residue — there is no `q=±1` diagonal generating it. So `{direction + Aut-family + character}` covers
the *algebra* (braids) but not the *topology* (knots): the missing structure is a
**relation/quotient the readings must respect but cannot generate**.

## Note for the technique — does knots stress the model? YES, and it reveals two genuine gaps.

This is the **first clean partial-break** in the notebook (25 prior decompositions, no break). The
break is informative, not fatal — it isolates *exactly* what the calculus lacks:

**Gap 1 — a knot invariant is NOT a character (the skein relation is not the character arrow).**
Every prior "invariant" in this notebook (`det2_mul`, `vp_mul`, `psign_mulPerm_hom`, entropy
additivity, Noether) was the **same** operation-preserving arrow `×↦·`/`×↦+` — a homomorphism out of
the composition family. The Jones polynomial is **not** such a homomorphism: it satisfies a
**three-term skein relation linking `L₊, L₋, L₀`** (over-crossing, under-crossing, and the
*smoothing* that has no crossing). The smoothing `L₀` is **a different construction `C`, not a
different reading of the same `C`** — it changes the strand count locally. The calculus's character
slot reads *one* `C`'s build-operation into a target operation; it has **no slot for a relation that
mixes three distinct constructions**. The writhe (signed crossing count, the abelianisation `Bₙ→ℤ`)
**is** a genuine character — it is literally `det`'s `q=±1` sign-count — but the writhe is *not* a
knot invariant (it changes under Reidemeister I). So the calculus captures precisely the part that
**fails to be a knot invariant**, and loses precisely the part that makes Jones topological. Honest:
the promotion "`q=±1` → formal `t`" is **wishful** — `t` is not a graded direction bit, it is the
bookkeeping variable of a *resolution-of-crossings recursion* (the Kauffman bracket state sum), which
is a different structure entirely.

**Gap 2 — the isotopy quotient is a residue the calculus cannot generate.** Every residue so far was
tagged `q=±1` and **generated by the reading's own self-application**: Cantor's diagonal (`q=−1`,
`object1_not_surjective`), φ's fixed point (`q=+1`), `ω` (cofinal heights), homology (`ker∂/im∂`).
The knot — the isotopy class of a braid closure — is a residue of a **topological quotient
(Reidemeister/Markov moves) imposed from a continuous ambient space**. There is no diagonal, no
fixed-point asymptote, no self-pointing that produces it. The `q=±1` residue tag, which absorbed
every prior limitative phenomenon, **does not apply** — the knot's "sameness" comes from continuous
deformation in `S³`, and the calculus has **no construction for the ambient 3-space** (it builds
`Real213` cuts, not embeddings/isotopies). This is the honest edge: *the calculus has discrete-
combinatorial quotients (kernel-coincidence `LensIso`, the closure monad `clo`, Galois) but no
topological-isotopy quotient*, and a knot invariant lives or dies by exactly that quotient.

**What braids reveal is MISSING from the calculus:**

1. **A relation-among-distinct-constructions primitive (the skein triple `L₊/L₋/L₀`).** The model has
   readings that *compose* (series), form *families* (`Aut`), and form *adjoint pairs* (Galois) — all
   relating readings of **one** `C`. It has **no apparatus for a linear relation tying three
   different `C`'s** (over, under, smoothed). This is genuinely new: it is neither the character arrow
   nor the `q=±1` residue. (Closest repo shadow, and it is only a shadow: the `∂²=0` *pairwise* sign-
   cancellation in `homology.md` relates two removal-orders of one cell — but that is two readings of
   one `C`, not three `C`'s; the skein relation is strictly richer.)

2. **A topological-isotopy quotient (the Markov/Reidemeister moves).** The calculus's quotients are
   all algebraic kernel-coincidences (`lensIso_iff_kernel_eq`) or closure operators (`clo`). The
   isotopy quotient is not a kernel of any reading the calculus can write — it requires an **ambient
   3-manifold and continuous deformation**, which has no `Raw`/`Lens` construction here. (Note: the
   repo's "two-axis braid" `(m,k)↦(2m+k,m+k)` in `MobiusProbeTwist` is an *unimodular `SL₂(ℤ)`*
   map — `det=1`, the `q=+1` Cassini pole — and is **honestly not** topological braiding; the name
   collision is exactly the trap the calculus must not fall into.)

**Where it does fit (so the break is precisely located, not total):** the braid *group* itself
EXTENDS with no new primitive — `Bₙ = ⟨n strands | crossing-compositions⟩` is `groups.md`'s
`Aut`-family with the **braid relation** as an extra relator, and the repo *has* the braid relation
in the only place it could (`(ts)³=e`, the Coxeter relator for Sym(3), `c3_chain_master` (f)) —
i.e. the calculus reaches the **permutation image** `Bₙ→Sym(n)` (forget direction → keep swap) but
**stops at the kernel** (the pure-braid / linking data), which is exactly the topologically
non-trivial part. The over/under direction bit `q=±1` is real and correctly identified; it is the
*promotion of that bit to the Jones variable `t` via a skein recursion* and the *isotopy quotient*
that the calculus cannot express.

---

### Verified Lean anchors (only real ones — knot/braid theory proper is ABSENT)

- **No knot/braid theory exists in `lean/E213/`.** `grep knot|braid|Jones|skein|Reidemeister`:
  - `hknotper` (`PisanoPeriodMinimal.lean`, `FibonacciApparition.lean`) — "not-period" var name,
    false positive.
  - "two-axis braid" (`ProbeTwist/ProbeTwistFixedPoint.lean`, `Mobius/MobiusProbeTwist.lean`,
    `Real213/INDEX.md`) — **metaphor** for the Möbius probe-twist `(m,k)↦(2m+k,m+k)`, an `SL₂(ℤ)`
    `det=1` map, **not** topological braiding.
  - **The one real structural hit:** `Lib/Physics/Symmetry/C3ChainCapstone.lean:c3_chain_master`
    part (f) — `braid relation (ts)³ = e` (the Coxeter presentation closing Sym(3)); generators
    `s,t` are involutions (parts (e),(h)). This is the **braid-relation analogue** the calculus can
    actually anchor to — at the *Sym(n)* (permutation-image) level only.
- **Structural analogues the FIT rests on** (the braid-*group* part):
  - `Lib/Math/Algebra/Linalg213/PermGroup.lean`: `composeList`, `composeList_assoc`,
    `composeList_invPerm_left` (the `Aut`-family = composition-closed self-readings; a crossing's
    inverse = the undo-reading).
  - `Lib/Math/NumberTheory/ModArith/Zolotarev.lean`: `mulPerm_comp` (Cayley: multiplication ↦
    composition), `psign_mulPerm_hom` (the `±1` sign character — the only genuinely
    operation-preserving "invariant", = the writhe's sign-count, but **not** a knot invariant).
  - `Lib/Math/Algebra/CassiniUnimodular.lean`: `det_step`, `det_closed`,
    `cassini_law_one_at_two_multipliers` (the `q=±1` orientation bit = over/under, verified; the bit
    is real, its **promotion to the formal Jones `t`** is what the calculus lacks).
  - `Lib/Math/NumberSystems/Real213/Markov/UnimodularSynthesis.lean:unimodular_four_readings`,
    `SternBrocotMarkov.lean:det2_mul` (the character `mul↦·` — the *shape* a knot invariant would
    need but provably is *not*, because Jones is not a homomorphism out of `Bₙ`).
- **Cross-frame:** `groups.md` (`Aut`-family), `determinant.md` (`q=±1`/`det`), `homology.md`
  (`∂²=0` pairwise sign-cancel — the closest shadow of a multi-term relation, and still strictly
  weaker than the skein triple).
