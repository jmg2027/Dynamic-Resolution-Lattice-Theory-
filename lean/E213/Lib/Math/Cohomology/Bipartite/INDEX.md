# `Cohomology/Bipartite/` — K_{NS,NT}^{(c)} multigraph cohomology

The bipartite-multigraph cohomology programme: concrete K-instances,
the filled-cell tower above K_{3,2}^{(c=2)}, Massey products,
Steenrod operations, and the `(NS, NT, c)`-parametric closure
(`Parametric/`, own INDEX).

## Concrete K-instances (V-series)

  - `V22.lean` — K_{2,2}^{(c=2)}
  - `V31c2.lean` — K_{3,1}^{(c=2)} (star with 2-multiplicity)
  - `V32.lean` / `V32Betti.lean` / `V32LocalSignature.lean` —
    K_{3,2}^{(2)} + Betti numbers + local (2,1,3) signature
  - `V33.lean` / `V33c3.lean` — K_{3,3}^{(c=2)} and K_{3,3}^{(c=3)}
  - `V43.lean` — K_{4,3}^{(c=2)}

## Filled-cell tower (higher cohomology above the 2-skeleton)

  - `Filled.lean` — higher cohomology via 2-cell filling
  - `Filled3Cell.lean` / `Filled3CellCohomology.lean` /
    `Filled3CellExtension.lean` — 3-cell extension + cohomology functor
  - `Filled4CellExtension.lean` / `Filled5CellExtension.lean` /
    `Filled5CellMultiExtension.lean` — 4-/5-skeleton, multi-5-cell
    for non-vacuous H⁵
  - `H1K.lean` — H¹(K_{3,2}^{(c=2)}) as explicit ℤ/2-module of rank 8

## Massey products

  - `MasseyTripleH1Witness.lean` / `MasseyTripleH1Multi.lean` —
    non-vacuous triples at the 2-skeleton
  - `MasseyFourFoldH1.lean` / `MasseyNFoldSchema.lean` /
    `MasseyAlternatingUniversal.lean` — 4-fold, n-fold schema,
    universal alternating ∀n
  - `MasseyTripleOmega.lean` — ⟨ω, ω, ω⟩ at the multi-5-cell
  - `V33MasseyWitness.lean` / `V33MasseyMulti.lean` /
    `V33Massey4Fold.lean` / `V33Indeterminacy.lean` /
    `V33c3Indeterminacy.lean` — the K_{3,3} Massey family

## Steenrod / Adem / cup structure at K_{3,2}

  - `SteenrodSquaresAtOmega.lean` / `Sq2At4Cell.lean` — Sq^i on face
    cohomology, chain-level Sq² at the 4-skeleton
  - `CartanAtTruncation.lean` / `AdemUniversal.lean` — Cartan at the
    C⁴ truncation, Adem relations (vacuous at truncation)
  - `FaceCup1At3Cell.lean` / `FaceCupHigher.lean` — cup_1 bridges
  - `SelfPairingTrace.lean` — bilinear self-pairing trace = (L¹-norm)²

## K_{3,3} enriched 2-complex (Direction A/C)

  - `V33Enriched.lean` / `V33c3Enriched.lean` — mult-layer faces,
    codim ≥ c
  - `V33EnrichedParametric.lean` — parametric in c
  - `V33EnrichedParametricDualSpan.lean` /
    `V33EnrichedParametricDualSpanHard.lean` /
    `V33EnrichedParametricDualSpanHardLift.lean` —
    per-layer completeness, HARD direction + ∀c lift
  - `V33CupDescent.lean` / `V33OppositeCup.lean` /
    `V33Mult1Trivial.lean` — cup descent + triviality results

## Möbius state classes

  - `Mobius213K32StateClass.lean` / `Mobius213K33StateClass.lean` /
    `Mobius213K33c3StateClass.lean` — vertex/edge cochains under the
    Möbius P

## Sub-cluster

  - `Parametric/` — `(NS, NT, c)`-parametric framework + universal
    Betti closure; see `Parametric/INDEX.md`

## Top-level

  - `Bipartite.lean` umbrella aggregator (one level up)
