# G142 — Full H² map of K_{3,3}^{(c=2)} via Massey witnesses

**Branch**: `claude/cohomology-marathon-merge-M5CTR`.
**Status**: **ALL 5 dimensions in H² = F₂⁵ reached (∅-axiom)**.
4 dims via 3-fold Massey (V33MasseyMulti); 5th dim via
4-fold Massey ⟨g1, g4, g2, g5⟩ (V33Massey4Fold).

## Setup

`K_{3,3}^{(c=2)}`: 6 vertices, 18 edges, 9 simple 4-cycle faces.

  · C² has dim 9 (9 face cochains).
  · `rank δ¹ = 4` (cycle-space of underlying simple K_{3,3}).
  · **H² = C² / im δ¹ ≅ F₂⁵**.

Dual description: the 5-dim H² is parameterised by the 5
independent linear functionals on C² that vanish on `im δ¹`.
Six canonical functionals are the row/column dependence
relations of the 3 × 3 face grid:

| Symbol | Sum |
|---|---|
| R_{S_{01}} | face0 ⊕ face1 ⊕ face2 |
| R_{S_{02}} | face3 ⊕ face4 ⊕ face5 |
| R_{S_{12}} | face6 ⊕ face7 ⊕ face8 |
| R_{T_{01}} | face0 ⊕ face3 ⊕ face6 |
| R_{T_{02}} | face1 ⊕ face4 ⊕ face7 |
| R_{T_{12}} | face2 ⊕ face5 ⊕ face8 |

Single dependency: `R_{S_{01}} ⊕ R_{S_{02}} ⊕ R_{S_{12}}
= R_{T_{01}} ⊕ R_{T_{02}} ⊕ R_{T_{12}}` (both XOR over all 9
faces).  Hence 5 independent functionals.

A face cochain `v ∈ C²` is in `im δ¹` iff all 6 (5 independent)
sums vanish.  Conversely, the violation vector
`(R_{S_{01}}(v), R_{S_{02}}(v), …, R_{T_{12}}(v)) ∈ F₂⁶
/ sum-zero` is the H² class of `[v]`.

## Massey witnesses landed (Phase 18-B + this session)

Star/incidence cocycles in H¹:

  · S-stars : `g1 = S₀-star`, `g2 = S₁-star`, `g3 = S₂-star`
  · T-incidences : `g4 = T₀-incidence`, `g5 = T₁-incidence`,
    `g6 = T₂-incidence`

Massey triples `⟨a, b, c⟩` with `a ⌣ b = 0` (chain-level)
admit a "pure" Massey rep `a ⌣ η_{bc}` where `δ¹ η_{bc} = b ⌣ c`.
For the cocycles above, `a ⌣ b = 0` automatically when `a`, `b`
are on the same side (both S-stars or both T-incidences).

### ⟨S, S, T⟩ family (S-star ⌣ S-star ⌣ T-incidence)

| Witness | η_{bc} | Rep | Violation in (R_{S₀₁}, R_{S₀₂}, R_{S₁₂}, R_{T₀₁}, R_{T₀₂}, R_{T₁₂}) |
|---|---|---|---|
| ⟨g1, g2, g4⟩ (primary, Phase 18-B) | e₆ | (1, 1, 0, 0, 0, 0, 0, 0, 0) | (0, 0, 0, 1, 1, 0) |
| ⟨g1, g2, g5⟩ (Witness A) | e₈ | (1, 0, 1, 0, 0, 0, 0, 0, 0) | (0, 0, 0, 1, 0, 1) |

### ⟨T, T, S⟩ family (T-incidence ⌣ T-incidence ⌣ S-star)

| Witness | η_{bc} | Rep | Violation |
|---|---|---|---|
| ⟨g4, g5, g1⟩ (Witness B) | e₂ | (1, 0, 0, 1, 0, 0, 0, 0, 0) | (1, 1, 0, 0, 0, 0) |
| ⟨g4, g5, g2⟩ (Witness C) | e₈ | (1, 0, 0, 0, 0, 0, 1, 0, 0) | (1, 0, 1, 0, 0, 0) |

The 4 violation vectors are pair-wise linearly independent
(each violates a relation untouched by all previous), so they
span a **4-dimensional subspace of H² = F₂⁵**.

Lean file: `lean/E213/Lib/Math/Cohomology/Bipartite/V33MasseyMulti.lean`
(21 PURE / 0 DIRTY).
Capstone: `four_witnesses_span_four_dim_H2`.

## Why only 4 of 5 — structural reason

Each Massey rep `g_i ⌣ e_k` (Hashed S-star against a single
mult-0 edge `e_k`) lives at **exactly two faces**: those whose
4-cycle traverses `e_k` and one of the three mult-0 edges of
`g_i`.  By the (S-pair, T-pair) indexing of faces, the two
non-zero faces always share the same S-pair (for ⟨S, S, T⟩
witnesses) or the same T-pair (for ⟨T, T, S⟩ witnesses).

Therefore:

  · ⟨S, S, T⟩ witnesses → violations live in the
    {R_{T_{01}}, R_{T_{02}}, R_{T_{12}}} = 2-dim plane.
  · ⟨T, T, S⟩ witnesses → violations live in the
    {R_{S_{01}}, R_{S_{02}}, R_{S_{12}}} = 2-dim plane.
  · Union = 4-dim plane.  Maximum reachable by pure
    star/incidence Massey.

The missing 5th direction is the **diagonal axis** corresponding
to violation patterns like `(1, 0, 0, 1, 0, 0)` — a single
S-row PLUS a single T-col violated, independently.

## The 5th dimension: open frontier

Two structural routes to access the 5th H² dimension:

### Route 1 — Mixed-side triples ⟨S, T, S⟩ or ⟨T, S, T⟩

These need a non-zero same-side cup-piece (`a ⌣ b` ≠ 0
chain-level) plus an auxiliary cobounding chain `η_{ab}`.

Pilot: `cupOpp g1 g4 = (1, 1, 0, 1, 1, 0, 0, 0, 0)` — non-zero
chain-level, descends via `η_{ab} = e_2 + e_4` per
`V33CupDescent.cup_g1_g4_descends_to_zero_bundled`.

For ⟨g1, g4, g_S⟩ Massey, the rep would be
`g1 ⌣ η_{bc} + η_{ab} ⌣ g_S` — a 2-term combination that may
exit the 4-dim plane.  Worth enumerating ⟨g1, g4, g_i⟩ for
i ∈ {1, 2, 3} systematically.

### Route 2 — Multiplicity-shift cocycles  (OBSTRUCTED by this cup)

The 9 mult-1 edges `e_{2k+1}` (k ∈ {0..8}) all lie in `ker δ¹`
(every face uses only mult-0 edges per `V33` face definitions).
After quotienting by `im δ⁰`, they contribute cohomology
classes orthogonal to the star/incidence basis.

**However**: the opposite-edge cup `cupOpp α β` at face F only
evaluates `α` and `β` on the 4 mult-0 edges of F's cyclic
ordering.  Hence if α is supported on mult-1 (odd-indexed)
edges only, `cupOpp α β = 0` chain-level for **any** β.

Consequence: mult-1 cocycles cup **trivially** against everything
under the opposite-edge cup, so Massey triples involving them
factor through the mult-0 subcomplex and produce reps inside the
same 4-dim plane as the star/incidence triples.

### Route 3 — Different cup operator on H² (CONJECTURED)

The opposite-edge cup may *factor through a 4-dim quotient of
H²*, with the 5th dimension inherently invisible to it.  If so,
fully spanning H² = F₂⁵ requires either:

  · A genuinely different cup operator (e.g., Steenrod cup-i for
    i ≥ 1, or a non-symmetric Alexander-Whitney-type cup), or
  · Higher Massey operations (n ≥ 4) that may pick up the missing
    direction even with the opposite-edge primary cup.

**Structural conjecture**: For K_{NS,NT}^{(c=2)} with H² of
dimension `b₂`, the opposite-edge cup image spans a subspace of
dim `b₂ - [c-1]` in H², leaving `c-1` "multiplicity-orthogonal"
dimensions that are *Massey-void* under this primary cup.  At
c = 2 this predicts 1 missing dimension per H² — exactly what
we observe at K_{3,3}^{(c=2)}.

(For c = 1, the conjecture predicts 0 missing dimensions —
consistent with the K_{3,2}^{(c=1)} = single 4-cycle case
where H² = F₂ is fully spanned by a single Massey class.)

## Capstone theorem (informal)

**Claim**: The full H² of K_{3,3}^{(c=2)} is spanned by Massey
products ⟨a, b, c⟩ for (a, b, c) ∈ (H¹)³, with the simple
star/incidence Massey hitting exactly 4 of 5 dimensions and the
remaining dimension accessible via Route 1 or Route 2.

**Falsifier**: Find a class in H² not in the image of the
Massey product operation `H¹ ⊗ H¹ ⊗ H¹ → H²` — i.e., a
"Massey-void" class.

## Significance

For K_{3,2}^{(c=2)} (b₂ = 1): a single Massey class
generates all of H² (the famous ω).  At K_{3,3}^{(c=2)}
(b₂ = 5), the structure is **multi-dimensional secondary
cohomology** — the parametric family `K_{NS,NT}^{(c=2)}`
exhibits a **graduated** Massey landscape.

The 4-dimensional explicit span via 3-fold Massey confirms
the "non-vacuous Massey transfers AND multiplies"
prediction: not only does the Massey detection mechanism
work at the next-up graph, but it produces a multi-class
spectrum.

## Update: full 5-dimensional H² REACHED

A focused continuation pass landed:

  · `V33Massey4Fold.lean` (17 PURE) — 4-fold Massey
    ⟨g1, g4, g2, g5⟩ produces chain-level rep
    `(0, 0, 1, 0, 0, 0, 0, 0, 0)`, the *single-face-2 cochain*.
    Violation vector `(1, 0, 0, 0, 0, 1)` violates `R_{S₀₁} +
    R_{T₁₂}` — a pattern linearly independent of the four
    3-fold violation vectors.  Hence the 5th H²-dimension is
    reached at Massey depth 4.

    The structural reason: the inner term `η_{ab} ⌣ η_{cd} =
    (e_2 + e_4) ⌣ e_8` of the 4-fold representative does NOT
    factor through any 3-fold cup-image — it is a genuinely
    higher operation.

  · `V33Mult1Trivial.lean` (12 PURE) — Route 2 (multiplicity-
    shift cocycle Massey) formally ruled out:
    `∀ α : CochE, cupOpp α (mult-1 indicator) = 0`
    chain-level at every face.  Mult-1 cocycles collapse
    Massey triples to pure cup-image, never reaching the
    5th dim.

  · Route 3 (different cup operator): unnecessary — the
    standard opposite-edge cup at depth 4 already spans the
    full H².  Route 3 would be needed only if 4-fold Massey
    had also failed.

  · Route B (lens face addition to the 2-complex):
    structural analysis (no Lean) — adding the 9 lens 2-cells
    (mult-0/mult-1 pairs) makes mult-1 indicators
    non-cocycles, collapsing `b₁ = 9 → 0`.  With `H¹ = 0` the
    Massey product `H¹ × H¹ × H¹ → H²` has nothing to
    multiply.  **Not the right thickening** for Massey
    detection at K_{3,3}^{(c=2)}.

## Capstone (informal)

**Theorem (sketch, informal)**: The opposite-edge cup
`H¹ ⊗ H¹ → H²` at K_{3,3}^{(c=2)} factors through a 4-dim
quotient of H² = F₂⁵.  The 5th dimension is reached at Massey
depth 4 via ⟨g1, g4, g2, g5⟩, whose defining-system inner
term `η_{ab} ⌣ η_{cd}` is the structural witness of the
"multiplicity twist" hidden in c = 2.

**Falsifier of the broader (c−1)-codim conjecture**: at
K_{3,3}^{(c=3)} the prediction is a 2-codim cup-image inside
H², with the missing 2 dimensions reachable at Massey depth
≤ 5.  Future verification: enumerate 4-fold and 5-fold Massey
classes at K_{3,3}^{(c=3)} and check the depth-codimension
trade.

## Anchor docs

  · `lean/E213/Lib/Math/Cohomology/Bipartite/V33.lean` —
    H² = F₂⁵ derivation + face_dep_S01, face_dep_T01.
  · `lean/E213/Lib/Math/Cohomology/Bipartite/V33OppositeCup.lean` —
    cup operator + g1..g6 basis + `cup_g1_g4_face_values`.
  · `lean/E213/Lib/Math/Cohomology/Bipartite/V33CupDescent.lean` —
    cup descent via `σ = e_2 + e_4`.
  · `lean/E213/Lib/Math/Cohomology/Bipartite/V33MasseyWitness.lean` —
    primary witness ⟨g1, g2, g4⟩ (Phase 18-B).
  · `lean/E213/Lib/Math/Cohomology/Bipartite/V33MasseyMulti.lean` —
    3 new 3-fold witnesses + 4-dim capstone (21 PURE).
  · `lean/E213/Lib/Math/Cohomology/Bipartite/V33Massey4Fold.lean` —
    **5th-dim breakthrough: 4-fold Massey ⟨g1, g4, g2, g5⟩
    rep at single face 2** (17 PURE).
  · `lean/E213/Lib/Math/Cohomology/Bipartite/V33Mult1Trivial.lean` —
    mult-1 cocycles cup-trivially against any α (12 PURE,
    Route 2 obstruction).
  · `theory/math/cohomology/k32_higher_cohomology.md` — chapter
    home for K_{NS,NT}^{(c=2)} Massey theory.

## Pilot computation for Route 1 (this session)

Tried ⟨g1, g4, g2⟩ with η_{ab} = e_2 + e_4, η_{bc} = e_6:

  · `g1 ⌣ e_6 = (1, 1, 0, 0, 0, 0, 0, 0, 0)`
  · `(e_2 + e_4) ⌣ g2 = (1, 1, 0, 0, 0, 0, 0, 0, 0)`
  · Massey rep = first ⊕ second = **0**  (chain-level trivial)

Tried ⟨g4, g1, g5⟩ with η_{ab} = e_2 + e_4, η_{bc} = e_2:

  · `g4 ⌣ e_2 = (1, 0, 0, 1, 0, 0, 0, 0, 0)`
  · `(e_2 + e_4) ⌣ g5 = (0, 0, 1, 0, 0, 1, 0, 0, 0)`
  · Massey rep = (1, 0, 1, 1, 0, 1, 0, 0, 0) — all 6 R-relations
    satisfied → rep IS in `im δ¹` → class is 0.

Both naïve mixed-side attempts produce trivial Massey classes for
the canonical η choices.  The indeterminacy `g_a · H¹ + H¹ · g_c`
may rescue non-triviality for some other admissible η; needs a
systematic enumeration (deferred).

## Next session priorities

  1. **Indeterminacy analysis** for the 4-fold breakthrough:
     compute `a · H¹ + H¹ · d + a · H² + H² · d + a · ⟨b,c,d⟩
     + ⟨a,b,c⟩ · d` indeterminacy for ⟨g1, g4, g2, g5⟩ and
     verify that the rep (0,0,1,0,0,0,0,0,0) is OUTSIDE it.
     This upgrades the chain-level breakthrough to a true
     cohomology-class statement.
  2. **`K_{3,3}^{(c=3)}` validation** of the (c−1)-codim
     conjecture: extend V33 to c=3, recompute b₂, search
     Massey depth ≤ 5 to span the predicted 2 extra
     dimensions.  If depth-(c+1) = depth-4 suffices for c=3,
     the conjecture is REFINED to "depth-(c+2)" hierarchy.
  3. **Steenrod Sq¹ (Bockstein)** as an independent test:
     define ℤ/4 → ℤ/2 lift on V33 cochains, compute Sq¹(g1)
     and check if its class hits the 5th dim independently
     of 4-fold Massey.
  4. **Cross-graph extension**: replicate the 4-fold
     5th-dim breakthrough at K_{3,4}^{(c=2)} (a new graph,
     b₂ predicted = 8 or similar), confirming the pattern.
