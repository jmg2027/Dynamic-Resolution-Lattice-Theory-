# G143 — c-multiplicity hierarchy at K_{3,3}^{(c)}: literal conjecture falsified, refined

**Branch**: `claude/cohomology-marathon-merge-M5CTR`.
**Status**: c=3 verification complete (29 PURE).  Literal
`(c−1)`-codim depth-`(c+2)` extrapolation is FALSE under the
simple-cycle face structure.  Cup image has codim 1 and depth-4
Massey suffices for ALL `c ≥ 2`.

## Setup

Direct extension of `V33` to multiplicity `c = 3`:

  · 6 vertices, 27 edges (3 mults × 9 vertex pairs)
  · 9 simple 4-cycle faces using only mult-0 edges
    (same face structure as V33, just renumbered)
  · `H¹ = F₂¹⁸` (vs F₂⁹ at c=2; 9 mult-1 + 9 mult-2 differences)
  · `H² = F₂⁵` (SAME as c=2 — face structure unchanged)

Lean: `lean/E213/Lib/Math/Cohomology/Bipartite/V33c3.lean`.

## What the c=3 file proves

| Theorem | Content |
|---|---|
| `c3_cup_g1_g4_values` | `g1 ⌣ g4 = (1,1,0,1,1,0,0,0,0)` chain-level, IDENTICAL to c=2 |
| `c3_eta_ab_cobounds_g1_g4` | `δ¹(e_3 + e_6) = g1 ⌣ g4` — η_ab choice transports |
| `c3_eta_cd_cobounds_g2_g5` | `δ¹(e_12) = g2 ⌣ g5` — η_cd choice transports |
| `c3_rep4_face_values` | `(e_3 + e_6) ⌣ e_12 = (0,0,1,0,0,0,0,0,0)` — single face-2 |
| `c3_cupOpp_alpha_m1_universal_face0` | mult-1 cup-trivial against any α |
| `c3_cupOpp_alpha_m2_universal_face0` | **NEW** mult-2 cup-trivial against any α |
| `c3_conjecture_refined` | Master capstone bundling the above |

The 4-fold breakthrough rep formula `η_{ab} ⌣ η_{cd}` produces
**the same single-face-2 cochain** at c=3 as at c=2, modulo the
edge-index isomorphism `e_{2k} ↦ e_{3k}` between c=2 and c=3
mult-0 sublattices.

## Why the (c−1)-codim conjecture fails

The structural reason is sharp.  Under the simple-cycle face
complex (only 4-cycles using mult-0 edges):

  1. Cup operator `cupOpp` at each face evaluates cocycles
     ONLY at the 4 mult-0 edges of that face's cyclic
     ordering.
  2. mult-`m ≥ 1` cocycles return `false` at every mult-0
     index, so the diagonal-pair contributions all vanish:
     `cupOpp α (mult-≥1 indicator) = 0` chain-level for any α.
  3. The cup image in H² is therefore entirely determined by
     mult-0 cocycles, which span a 5-dim subspace of H¹ — the
     same subspace at c=2 and c=3.
  4. The 4-dim cup-image plane in H² inherits from the
     mult-0 sub-Massey, independent of c.

Hence codim of cup image = 1 for ALL `c ≥ 2`, NOT `c − 1`.

The depth-4 Massey breakthrough also transports verbatim: the
inner term `η_{ab} ⌣ η_{cd}` lives entirely in the mult-0
sublattice and produces the single-face-2 rep regardless of c.

## Where did the "c-counter" really go?

Gemini's intuition that "mult-≥1 cocycles count `c`" is
*correct at the H¹ level*: `dim H¹ = 9c` (= 9 stars + 9·(c−1)
mult-shift cocycles).  But this `c`-dependence sits in H¹, not
in H², and the cup operator under this face complex doesn't
transport it across.

The "c-counter" thus belongs to a different invariant.  Three
candidate venues for the genuine `c`-dependent structure:

### Candidate A — Richer 2-complex

Include 4-cycles that use higher-multiplicity edges (e.g.,
mixed mult-0 / mult-1 cycles).  At c=2 there are 16 choices
of multiplicity per (S-pair, T-pair) = 144 candidate faces;
their cycle space has structure that the V33 setup
deliberately ignores.  A 2-complex incorporating ALL of these
would have H² growing with c, potentially giving
`(c−1)`-codim cup image relative to a `c`-dependent H².

### Candidate B — Higher cohomology H³ / H⁴

Add 3-cells (filled solid tori from the mult-pair lenses).
Higher cohomology may pick up the c-counter in a way the
2-cohomology cannot.  Pilot: at K_{3,2}^{(c=2)} we have
`Filled5CellExtension` and Steenrod squares at
`H² ω` — analogous 5-cell extensions at K_{3,3}^{(c)} likely
have `c`-dependent structure.

### Candidate C — Bockstein Sq¹

`Sq¹: H¹(F₂) → H²(F₂)` is the F₂ reduction of the connecting
map of the short exact sequence `0 → ℤ/2 → ℤ/4 → ℤ/2 → 0`.
At c≥2 the multi-edge structure carries a natural ℤ/4
refinement (e.g., labels `e_{2k}` as 0 and `e_{2k+1}` as 1
mod 2, but as 0 and 2 mod 4 — the lift carries multiplicity
information).  The Bockstein image in H² could differ from
the F₂ cup image in a `c`-dependent way.

### Candidate D (most likely) — c-counter in *Massey indeterminacy*

The 4-fold Massey class for ⟨g1, g4, g2, g5⟩ has
indeterminacy `a · H¹ + H¹ · d + a · H² + H² · d +
⟨a,b,c⟩ · d + a · ⟨b,c,d⟩`.  At c=3, `H¹` is *twice as big*
as at c=2.  The indeterminacy subgroup grows accordingly,
potentially absorbing the chain-level 5th-dim rep.

**This is the critical c-dependent check**: at c=2 the
indeterminacy does NOT contain `(0,0,1,0,…,0)` (would need
verification).  At c=3 the indeterminacy may grow to include
it, making the cohomology class trivial.  If so, the 5th
H²-dim at c=3 is unreachable not by depth-4 Massey class
existence, but by *indeterminacy growth*.

## Refined conjecture

**Refined (working) statement**: For the simple-cycle face
complex on `K_{NS,NT}^{(c)}` with `c ≥ 2`:

  · `dim H² = 5` independent of `c`
  · Cup image has codim 1 in H²
  · Massey depth 4 reaches the 5th dim *chain-level*
  · The "c-counter" lives either in the 4-fold Massey
    *indeterminacy* (Candidate D) or in a different
    cohomology invariant (Candidates A, B, C)

This is a **refinement, not a defeat** of the original
intuition.  The depth-4 chain-level breakthrough is now
unambiguous; the c-dependence has moved to indeterminacy /
higher invariants.

## Candidate D — RESOLVED (negative): ψ-discriminator survives at c=3

Phase 1 + Phase 2 complete, 25 PURE / 0 DIRTY.  The discriminating
functional ψ = R_{S₀₁} + R_{S₀₂} + R_{S₁₂} = XOR of all 9 face
values lifts rep₄ to a non-trivial H² cohomology class at BOTH
c=2 and c=3 under the simple-cycle face structure.

Key ψ identities (∅-axiom verified, both c):

  · `ψ(cupOpp g1 ξ) = 0 ∀ ξ : CochE` — for ALL edge cochains
    (no cocycle hypothesis), because g1's 3-edge support forces
    every relevant ξ-edge to appear an even number of times in
    the ψ-sum.
  · `ψ(cupOpp ξ g5) = 0 ∀ ξ : CochE` — symmetric argument.
  · `ψ(δ¹σ) = 0 ∀ σ : CochE` — each mult-0 face-cycle edge
    appears in exactly 4 (= even) faces.
  · `ψ(rep₄) = 1` — face 2 has the unique nonzero value.

Conclusion: principal 4-fold Massey indeterminacy
`g1 ∪ H¹ + H¹ ∪ g5` is killed by ψ at both multiplicities.
The c-multiplicity counter is therefore NOT in the indeterminacy.

**Refined Refined conjecture**: the c-counter must live in:

  · Richer 2-complex (Candidate A) — incorporate the 16
    multi-multiplicity 4-cycles per (S-pair, T-pair); recompute
    H² + cup image to look for a `(c−1)`-codim manifestation.
  · Higher cohomology H³ / H⁴ (Candidate B) — secondary level.
  · Steenrod Sq¹ via ℤ/4 lifts (Candidate C) — primary Bockstein.

Anchor formalizations:

  · `lean/E213/Lib/Math/Cohomology/Bipartite/V33Indeterminacy.lean`
    — c=2 ψ-discriminator + rep₄_outside_indeterminacy (14 PURE).
  · `lean/E213/Lib/Math/Cohomology/Bipartite/V33c3Indeterminacy.lean`
    — c=3 mirror + cross_frame_psi_discriminator (11 PURE).

## Anchor docs

  · `lean/E213/Lib/Math/Cohomology/Bipartite/V33c3.lean` —
    c=3 minimal port (29 PURE).
  · `research-notes/G142_K33_massey_full_h2_map.md` —
    parent doc with c=2 full-span breakthrough.
  · `lean/E213/Lib/Math/Cohomology/Bipartite/V33Massey4Fold.lean` —
    c=2 5th-dim breakthrough (17 PURE).
  · `theory/math/cohomology/k32_higher_cohomology.md` —
    chapter home (needs update to reflect refined conjecture).

## Next session priorities (post Candidate-D resolution)

  1. **Richer 2-complex** at c=2: incorporate the 16 multi-
     multiplicity 4-cycles per (S-pair, T-pair) and recompute
     H² + cup image.  See if `(c−1)`-codim manifests in this
     richer setting.  (Candidate A)
  2. **Bockstein Sq¹ infrastructure**: define ℤ/4 lifts of
     V33 cochains and compute `Sq¹(g1)` — independent test
     for the c-counter manifestation in H².  (Candidate C)
  3. **Higher cohomology H³**: compute H³ at K_{3,3}^{(c=2)}
     vs c=3 via a 3-cell complex extension.  (Candidate B)
