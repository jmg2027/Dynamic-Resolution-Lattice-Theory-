# Round 2 — synthesis: the trichotomy built, the symmetry law, the axis-polymorphic wall

*Integrates R2: ForcingToy (build), SectionCount (build), F (genericity), G (symmetry) + orchestrator H
(`H_orchestrator_R2_...`).  R1's picture is now machine-checked and refined.*

## R2 made R1 concrete (two ∅-axiom witnesses)

- **`ForcingToy.lean` (12/0 PURE)** — `forcing_toy_independence : glob g0 ≠ glob g1` (one construction, two
  generics, neither canonical) + `bundle_recovers_independence` (carry both σ over the poset, project
  per-condition = sheaf-over-poset, funext-free).  **"forcing = adjoining a free selection-σ" is now a
  built theorem**, the minimal Cohen-independence-as-Lens-parameter witness.
- **`SectionCount.lean` (16/0 PURE)** — the `0/1/many` trichotomy as a stated object: `inductive
  SectionCount`, `classify → wall/forced/free`, three built instances (`wall_no_total_section` /
  `forced_exists_unique` / `free_two_sections`) + `trichotomy_complete` + `trichotomy_distinct`.  **R1's
  central classification is now machine-checked.**

## The two refinements (F, G) — both sharpen R1, neither overturns it

**G — the symmetry law (CONFIRMED, with the Lean delegation chain):**  height-h's one-way asymmetry **is the
one diagonal on the strength axis** — grounded, not analogized: `height_diagonal_escapes := diag_not_in_seq`,
`ceiling_reference_leaves_residue := cantor_general` (= `object1_not_surjective`).  So **Burali-Forti = the
diagonal on the height fiber** (orchestrator Claim 1 confirmed via the actual chain).  THE LAW:

> **A free Lens parameter's symmetry-type is read off its fiber's order-structure** — *unordered* fiber ⟹
> symmetric (forcing; `ChoiceLens` `sigmaL ↔ sigmaR` interchangeable); *well-ordered* fiber ⟹ one-way
> asymmetric (large cardinals; `DepthHeightDiagonal` strictly-upward escape).

Refinement of R1: selection-σ and height-h are **not "B's two aspects"** but **the one B-escape over two
kinds of fiber** — fiber-order is a *frame coordinate*, not a second invariant.  (Sharper than orchestrator
H2/D; corrects them.)  This rederives the two axes of set-theoretic independence (forcing / large cardinals)
from a *single* distinction (fiber order).

**F — genericity (placed precisely):**  "generic" = **(the height-h limit of the refinement tower) on (a
free selection-σ), relative to (a nonexistent exterior M)**.  The "over M" clause **dissolves** (§5.1: no
privileged ground model).  "Meets every dense set" = "σ decides every stage" is *real* and is the **height-h
axis** (not selection).  Crucially (correcting orchestrator Claim 3): the generic is the **`q=+1` converge
limit** (reached-by-none cut, `Real213`-shaped), **NOT** the `q=−1` diagonal — so the diagonal stays the
unique wall, and "reached-by-none" splits converge (generic/cut) vs escape (diagonal), exactly the R1
two-reach-mode refinement.

## The unified picture after R2

- **One wall, axis-polymorphic** (orchestrator H Claim 2, G-confirmed for the height fiber): the *same*
  `no_surjection_of_fixedpointfree` appears once per fiber-type — Cantor (cardinality), Russell/Gödel/halting
  (self-reference), **Burali-Forti (ordinal height)**, and the generic's incompleteness (σ-completeness).
- **Free parameters = the approaches to it**, classified by **fiber order-structure** (the symmetry law):
  unordered → symmetric selection-σ (= forcing, `ForcingToy`); well-ordered → asymmetric height-h
  (= large cardinals).  Genericity = the height-limit of a selection-σ (F).
- **Section-count `0/1/many` = wall/forced/free** (`SectionCount`, built) **= the `q=±1` tag one level up.**

So the choice-correction has grown into a complete, machine-witnessed structural theory of the calculus's
boundaries: **one axis-polymorphic wall (the diagonal) + free parameters whose symmetry is their fiber's
order**, with forcing and large cardinals as the two fiber-order cases, and the whole thing the residue tag
read on the space of readings.

## Round 3 agenda (the open seams)

1. **`FiberSymmetry`** (G): build the biconditional "directed-escape ⟺ well-founded fiber" (one `diag` engine
   over `Bool` (undirected, symmetric) vs `ℕ`/`coordLt` (directed, asymmetric)).  Promotes the symmetry law
   from a reading to a theorem.
2. **The recurring THIRD STATUS** (R1 skeptic's `S³` missing-input + G's *partially-ordered* fiber):
   is there a genuine status beyond {wall, forced, free} and beyond {symmetric, asymmetric} — a
   *partial-order* fiber giving *partial* symmetry, mirroring "absence ≠ obstruction ≠ parameter"?  This is
   the seminar's own residue — investigate whether the trichotomy itself leaves a residue.
3. **`GenericAsCut`** (F): genericity as a `Real213`-cut-shaped pointing — "no finite σ_n decides every dense
   set" = `object1_not_surjective` on the selection tower.
