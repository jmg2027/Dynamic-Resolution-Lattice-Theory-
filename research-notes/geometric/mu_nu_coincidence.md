# The μF ≅ νF coincidence class — characterization (deep-research result)

*Resolves the open frontier of `static_dynamic_duality.md` ("for which readings
does static = dynamic?").  Classical scaffolding: Lambek 1968, Adámek 1974, Barr
1993, Smyth–Plotkin 1982, Aczel 1988.  Grounded in the repo's existing μF/νF
formalization.*

## The question

Each slash-reading is an endofunctor `F_R` with an initial algebra `μF_R`
(constructive / dynamic, "built from below") and a final coalgebra `νF_R`
(completed / static, "the object satisfying its consistency equation"); Lambek's
lemma makes both fixed points `X ≅ FX`, and initiality+finality give one canonical
comparison `ι : μF → νF`.  "static = dynamic (no residue gap)" is exactly **`ι` is
an isomorphism**.

## The characterization

> **Theorem (algebraicity criterion).**  For an ω-cocontinuous reading `F_R`, the
> following are equivalent:
> 1. `ι : μF_R → νF_R` is an isomorphism (static = dynamic);
> 2. **`R` is algebraic** — every element of `νF_R` is a directed sup of compact
>    (finitely-constructed, ∈ image ι) elements;
> 3. the initial ω-chain `0 → F0 → F²0 → …` converges **at ω** (no limit ordinal
>    `> ω` needed); equivalently `μF_R` is already Cauchy-complete in Barr's
>    depth ultrametric `d(x,y)=2^{−(first depth they differ)}`;
> 4. the residue `νF_R ∖ image(ι)` is empty.
>
> When these fail, `ι` is a **dense isometric mono that is not epi** (Barr: νF =
> Cauchy completion of μF), and the residue is exactly the **non-compact / limit
> elements** — a **Cantor diagonal surplus**: it is the cokernel of the
> finite-naming map `μF → (observations → values)`, whose non-surjectivity *is*
> Cantor's theorem (`object1_not_surjective = cantor_raw_bool`).

## The dividing line: glue

A fresh relation-object either **opens a new orthogonal axis** (free reading) or
**lands between/inside existing elements** (contractive reading).

| reading | F | μF (construct) | νF (complete) | algebraic? | ι iso? | residue |
|---|---|---|---|---|---|---|
| complete graph / simplex (free) | discrete sum (new axis) | finite `K_m`, edges `C(m,2)` | completed `K_ω` | **yes** | **YES (μF≅νF)** | ∅ |
| betweenness / midpoint | IFS, two ½-contractions | dyadic rationals | continuum `[a,b]` | no | no | irrationals, `2^ℵ₀` |
| mediant / Stern–Brocot | mediant IFS (`det=1`) | `ℚ_{>0}` (finite paths) | `ℝ_{>0}` (infinite paths) | no | no | irrationals, `2^ℵ₀` |
| Cantor set | `X ↦ X⊔X` (middle-third) | finite addresses | `{0,1}^ℕ` | no | no | aperiodic branches, `2^ℵ₀` |

Free = *discrete* polynomial functor, no glue, every element finitely born,
ω-chain converges at ω → **coincide**.  The others = *contractive* IFS, glue adds
Cauchy-limit points at stage ω → **gap = `2^ℵ₀` Cantor surplus**.

## Repo grounding (this is already half-built ∅-axiom)

- **Lambek fixed point**: `Theory/Raw/Lambek.{decompose,rebuild}`; `two_closures`
  (Lambek holds for νF too; well-foundedness selects μF).
- **μF well-founded floor**: `Lambek.isPart_wf`, `MuNuMirror.{no_infinite_descent,
  depth_cofinal, ascent_unbounded}`.
- **νF (the slash final coalgebra)**: `CoResidue.{SlashNu, slashNu_final,
  lAna_unique}` — the M-type finality, ∅-axiom (no coinduction primitive); the
  escapes `spineL`, `boolSpine` are named non-compact inhabitants.
- **ι mono, not epi**: `CoResidue.{rawToSlashNu_faithful, spineL_escapes,
  boolSpine_injects_bitstreams}` (the last = the `2^ℵ₀` surplus, stated
  ∅-axiom-honestly as a `Distinct`-preserving `(Nat→Bool) ↪ νF`, not a `Cardinal`
  claim).
- **gap = Cantor diagonal**: `FlatOntologyClosure.object1_not_surjective`
  (= `cantor_raw_bool`); and at the ordinal-tower supremum the diagonal recurs —
  `completeness_without_completeness.md` Part V `ceiling_residue_is_pointing_residue
  = cantor_general`.
- **the coincidence case, definitionally**: `AngleStructure/SimplexSelfForm.
  complete_step` (`edgesK(m+1)=edgesK m + m` by `rfl`) — μF≅νF for the discrete
  reading as a definitional equality.
- **the multi-axis ordinal meter**: `Cauchy/{DepthOrdinal.lex_wf (<ω²),
  DepthOmegaTower.coord_wf (<ω^r)}`, `DepthHeightDiagonal.height_diagonal_escapes`
  (no top) — the constructive "commuting growth axes" (this session) are the
  μF-side face of this analytic ordinal tower.

## Subtlety — the multi-axis stage and ω-cocontinuity

From cycle 2 the construction has multiple independent commuting growth axes
(confluence; `cycle_intermediate_lattice.md`), so the "stage" is a filtered
diagram over a directed poset, not a linear ℕ-chain.  This stays **ω-cofinal**
(hence ω-cocontinuous, hence convergence at ω, hence the free reading still
coincides) **whenever `F` is finitary** — each new object references only finitely
many priors.  The complete-graph reading is finitary (every vertex finitely born,
`√(2N)` active hubs; `free_graph_structure.md`), so it coincides.  A genuinely
*infinitary* reading (one combine referencing a whole infinite axis-family at
once) would break ω-cocontinuity and push the convergence ordinal past ω — an open
possibility, the sharpest place to look for a `>ω` gap on the carrier itself.

## Status and open items

- **Endpoints: closed ∅-axiom.**  Free coincides (`SimplexSelfForm`); contractive
  gaps (`object1_not_surjective`, `boolSpine`).
- **The biconditional itself: open (characterized, not mechanized).**  A
  Mathlib-free Lean lacks off-the-shelf ω-cocontinuous-functor / compact-element
  notions; mechanizing "algebraic ⟺ ι iso" is the principal next target.
- **νF carriers for the contractive readings: open.**  Lean builds νF only for the
  slash (`SlashNu`); the midpoint/mediant/Cantor νF (e.g. `Real213` cuts as the
  betweenness νF) and their non-surjective dense `ι` are unbuilt.
- **Cardinality `2^ℵ₀`** is a classical (C) reading; the (L) corpus has only the
  `Distinct`-preserving injection.

## One-line takeaway

**Static = dynamic ⟺ the reading is algebraic (no glue, all elements compact);
otherwise the gap is the Cantor diagonal (`object1_not_surjective`), of size
`2^ℵ₀`.  The simplex/complete-graph reading is the canonical algebraic
self-form; the continuum/Stern–Brocot/Cantor readings are the contractive
gap cases.**
