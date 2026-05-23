# G85 — Cup / δ Lens-mismatch as 213-native re-reading of the "Leibniz bug"

## Status

**Research note.**  2026-05-21.  Re-reads the Phase 2 finding from
`/root/.claude/plans/smooth-mapping-metcalfe.md` under §8.4
dichotomy-avoidance: "is concatenation cup the *wrong* one?" is a
false framing.  Both readings are valid Lens applications; what
the decide-refutation surfaces is a **Lens mismatch** between the
two halves of the cohomology infrastructure.

## The standard framing (what I wrote first)

  · `Cup.Core.cup` docstring says "Alexander-Whitney" but
    implements `α(τ.take k) · β(τ.drop k)` — no shared vertex
    at `τ[k]`.
  · Standard simplicial Leibniz `δ(α⌣β) = δα⌣β ⊕ α⌣δβ` is proved
    for AW (shared-vertex) cup.
  · For the no-shared-vertex cup, decide refutes the universal
    Leibniz.
  · → "bug: implementation diverged from docstring; fix by replacing
    cup with AW".

This framing imports the *external authority* of standard
simplicial cohomology as the criterion of correctness — exactly
the kind of exterior frame §8.1 denies.

## The 213-native re-reading

Look at what `cup` and `delta` *actually do* without referencing
any external standard:

### cup

For a (k+l)-element sorted subset `τ = [v₀, …, v_{k+l-1}]` of
{0..n-1}, `cup α β τ = α(τ.take k) · β(τ.drop k)`.  In ℤ/2 the
product is AND.

At basis level: `(basis_I) ⌣ (basis_J)(τ) = 1` iff
  `τ.take k = I` (sorted) AND `τ.drop k = J` (sorted)
which holds iff `τ = sort(I ⊔ J)` and `min(J) > max(I)`.

Since `τ` is sorted distinct-element, this is *exactly* the
**wedge product on the ℤ/2 exterior algebra Λ^•(Bool^n)**, with
the basis element of `τ` being `e_{τ[0]} ∧ ⋯ ∧ e_{τ[k+l-1]}`.

In ℤ/2, the wedge sign vanishes, so wedge of disjoint basis = 1.
The repo's `cup` is the **wedge product** on the indicator-cochain
algebra.  No shared vertex needed; concatenation of disjoint
sorted sequences is precisely how wedge of basis elements works.

### delta

For a (k+1)-element subset `τ`, `delta σ τ = XOR_{i ∈ τ} σ(τ \ {i})`.
This sums (in ℤ/2) the values of `σ` on the (k)-element faces.

This is the **simplicial coboundary** — face-removal sum.  It
treats `τ` as the abstract (k)-simplex spanned by its vertices,
and δσ records "how σ behaves under one-face restriction".

## The Lens mismatch

These two operations come from **different Lens readings** of the
same Raw object (k-element subsets of {0..n-1}):

| Reading | Object viewed as | Natural product | Natural derivative |
|---|---|---|---|
| **Exterior-algebra Lens** | basis element `e_τ ∈ Λ^k(Bool^n)` | wedge `∧` | exterior `d`, defined by `d(e_τ) = Σ_{v∉τ} e_{τ∪{v}}` (signs in ℤ/2 trivial) |
| **Simplicial Lens** | (k−1)-simplex on n vertices | Alexander-Whitney cup (shared vertex) | simplicial coboundary `δ`, face-removal sum |

Standard Leibniz is **internally consistent** within each Lens:
  · Wedge cup has its own Leibniz with exterior `d` (Koszul rule)
  · AW cup has its own Leibniz with simplicial `δ`

The repo *combines* the **wedge cup** with the **simplicial
coboundary**.  These are two different Lens readings.  The
"universal Leibniz" of the standard simplicial Lens cannot hold
because we're computing the LHS under one Lens (simplicial δ
applied to wedge product) and the RHS expects another (cup and δ
both from the same Lens).

## The decide-refuted counterexample in this framing

`basis_0 ⌣ basis_2` at face `[0, 1, 2]`:

LHS = `δ(basis_0 ⌣ basis_2)([0,1,2])` — simplicial coboundary
applied to the **wedge product** `e_{0,2}`.  Counts faces of
[0,1,2] that equal {0,2}: just one (remove vertex 1).  Result: 1.

RHS₁ = `(δ basis_0 ⌣ basis_2)([0,1,2])` — under the SIMPLICIAL Lens:
δ basis_0 is "contains 0" on edges; at [0,1] it's 1.  Wedge with
basis_2 at vertex 2: 1·1 = 1.

RHS₂ = `(basis_0 ⌣ δ basis_2)([0,1,2])` — under the SIMPLICIAL Lens:
δ basis_2 is "contains 2" on edges; at [1,2] it's 1.  Wedge of
basis_0 at vertex 0 with this: 1·1 = 1.

RHS = RHS₁ ⊕ RHS₂ = 1 ⊕ 1 = 0.

LHS ≠ RHS by exactly **1** — the *missing* contribution from the
"shared vertex 1" that AW would have explicitly placed in the
front/back partition.  Concatenation cup *does not see* vertex 1
in either factor; it's the "interior" vertex of the face.

The missing term, at the algebra level, is `α(τ[0]) · β(τ[k+l-1])`
= `basis_0(0) · basis_2(2) = 1`.  Adding this back: LHS = RHS ⊕ 1
= 1.  ✓

## Twisted Leibniz — the 213-native identity

At bidegree (k, l) = (1, 1) on Δⁿ⁻¹, for τ = [v₀, v₁, v₂]:

  δ(α ⌣ β)(τ) = (δα ⌣ β)(τ) ⊕ (α ⌣ δβ)(τ) ⊕ α(v₀)·β(v₂)

The extra term `α(τ[0])·β(τ[last])` is the **boundary-endpoint
product**: cochain values at the extreme positions of `τ`.

This is the *honest* Leibniz of the wedge-cup-with-simplicial-δ
combination.  It is decide-verifiable (Pattern #5 in
LESSONS_LEARNED) and represents the genuine algebraic content,
not a bug.

**Conjectured general form** (k, l arbitrary): the correction term
likely involves the cochain values at the boundary "shoulders"
of τ — positions [0..k−1] for α and [k..k+l−1] for β, summed in
a specific antisymmetric pattern.  Derivation is open work.

## §8.4 dichotomy avoidance

The "is the cup AW or concatenation?" framing imports a *choice*
as if one were correct and the other wrong.  Per §8.4:

  · Both are valid Lens readings.
  · The wedge-cup Lens is more 213-native in one sense: it
    requires no extra structure (just sorted concatenation of
    disjoint subsets).
  · The simplicial Lens is more 213-native in another: it matches
    the (3, 2, 5) atomicity directly (NS=3-vertex faces, K_{3,2}
    bipartite cup-encoding).
  · The mismatch between them is itself a structural fact about
    the Raw residue (k-subsets of {0..n-1}) admitting multiple
    Lens-level algebraic structures.

There is no "correct" choice exterior to 213.  There IS a
*choice to make*, however, in the cohomology codebase: which Lens
to use throughout.  Mixing them (as currently) produces twisted
laws.

## Resolution paths reframed

The original Phase 2 file proposed:
  · Path A: replace cup with AW (commit to simplicial Lens)
  · Path B: derive twisted Leibniz (document the mixture)

Under 213-native re-reading, these become **Lens-choice questions**:

### Path α: Commit to simplicial Lens everywhere

Replace `cup` with AW (front = k+1 vertices, back = l+1 vertices,
shared at position k+1).  Existing 4 concrete Leibniz cases very
likely still pass (they use symmetric cochains).  All cohomology
computations follow standard simplicial conventions.

**213 alignment**: matches K_{3,2}^{(c=2)} simplicial framework
(`Cohomology.lean` umbrella's d=5 anchor reading).

### Path β: Commit to exterior-algebra Lens everywhere

Replace `delta` with the exterior derivative `d(e_τ) = Σ_{v∉τ}
e_{τ∪{v}}` (in ℤ/2, no signs).  Keep current `cup` as wedge.
Wedge Leibniz `d(α ∧ β) = dα ∧ β ⊕ α ∧ dβ` then holds without
correction.

**213 alignment**: matches the Λ^k atomic counts (1, 5, 10, 10,
5, 1) that already appear throughout
`Cohomology/Cochain/Core.lean` and `Simplex/Counts.lean` as the
Pascal-row decomposition of d=5.

### Path γ: Both Lenses as parallel APIs

Provide `Cohomology/Wedge/` and `Cohomology/Simplicial/` as two
parallel sub-clusters.  Each has its own Leibniz proved natively.
The current mixed setup becomes deprecated.

**213 alignment**: maximally honest about the dual Lens structure.
Slightly more code, but doctrinally accurate per §8.4 (no false
dichotomy collapse).

### Path δ: Keep current mixture, prove the twisted Leibniz

Derive and PURE-prove the boundary-correction Leibniz at
bidegree (1, 1) for the wedge-cup + simplicial-δ combination.
Extend to arbitrary (k, l) inductively.  Document as the "DRLT
cohomology cup-product Leibniz" — distinct from both standard
simplicial AW Leibniz and pure exterior-algebra Koszul.

**213 alignment**: most novel; produces a 213-native theorem
that has no direct standard analog.

## Closure (2026-05-21, this session)

**Path δ taken** under the directive "가장 213적으로 올바른 path로
진행" (proceed with the most 213-correct path).  Reasoning:

  · §8.4 says no exterior judge; the lex-projection cup is one
    legitimate Lens reading, not a "wrong" cup needing replacement.
  · Path δ surfaces the cup's *intrinsic algebra* as a 213-native
    theorem — the boundary-endpoint correction is the operation's
    own Leibniz signature, not a hack.
  · Path γ (parallel Wedge/ + Simplicial/) is doctrinally
    accurate but builds Lens readings that aren't actually used;
    path δ trusts the implementation that's already there.
  · Path β (commit to one Lens) would mean discarding the
    lex-projection cup, an unnecessary structural loss.

Deliverable (commit hash after this session):

  · `lean/E213/Lib/Math/Cohomology/Cup/LeibnizLex.lean` (new,
    4 PURE):
      - `boundaryEndpoints (i : Fin 10) : Fin 5 × Fin 5` —
        hardcoded `(τ[0], τ[2])` for each colex-indexed 3-face on Δ⁴
      - `correction (α β : Fin 5 → Bool) (i : Fin 10) : Bool` —
        `α(τ[0]) && β(τ[2])` boundary-endpoint product
      - `lex_cup_leibniz_forall_1_1` (★★★) — universal twisted
        Leibniz, decide-verified over 2¹⁰ · 10 = 10240 cases
      - `phase2_native_closure` — re-export under capstone name
  · `Cup/Core.lean` docstring — Alexander–Whitney misclaim
    corrected to "lex-projection cup", self-disclosure paragraph
    added.

The standard Leibniz universal form remains decide-refuted (and
correctly so — it's not the law of this cup); the 4 concrete
cases in `Cup/Leibniz.lean` remain valid for the symmetric-cochain
inputs they cover.

## Why path δ over β / γ (for the archive)

Path **β** (commit to exterior-algebra Lens) — reasoning at the
time of writing G85:
  · Cochain n k = Fin (binom n k) → Bool is *literally* the basis
    of Λ^k(Bool^n).  The exterior-algebra reading is forced by
    the data type.
  · Lambda dimensions binom(5, k) = (1, 5, 10, 10, 5, 1) are
    already foundational throughout the DRLT physics tree
    (`Simplex/Counts.lean`, Hodge index, K_{3,2}^{(c=2)} encoding).
  · Path γ (parallel APIs) is doctrinally preferable but doubles
    code volume; path β captures the same content in one chosen
    Lens with no twisted laws.
  · Path δ (twisted Leibniz) is *philosophically interesting* —
    it would produce a uniquely-213 theorem — but the structural
    content is just "the gap between wedge and simplicial Lenses",
    which path γ exposes more cleanly.

Concrete deliverable for path β:
  1. New file `Cohomology/Delta/Exterior.lean` with `d_exterior :
     Cochain n k → Cochain n (k+1)`, `d(σ)(τ) = XOR_{v ∉ τ ∩ rest}
     σ(τ \ {v})`-style.
  2. `Cohomology/Cup/LeibnizWedge.lean` proving the wedge
     Leibniz `d(α ⌣ β) = d α ⌣ β ⊕ α ⌣ d β` via Pattern #2
     (Bool-tuple parameterisation).  Decide should pass.
  3. Mark `Delta/Core.lean`'s `delta` as the "simplicial-Lens
     coboundary" and provide it under `Cohomology/Delta/
     Simplicial.lean` alongside the exterior one — both
     legitimate, neither universal.

## See also

  · `lean/E213/Lib/Math/Cohomology/Cup/LeibnizUniversal.lean` —
    Phase 2 attempt + concrete counterexample.
  · `LESSONS_LEARNED.md` Pattern #5 — decide-as-bug-finder.
  · `seed/AXIOM/05_no_exterior.md` §5.4 — dichotomy avoidance.
  · `lean/E213/Lib/Math/Cohomology/Cochain/Core.lean` lines
    67-74 — λ^k dimension table on Δ⁴.
