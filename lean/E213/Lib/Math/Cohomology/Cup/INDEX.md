# `Cohomology/Cup/` — strict cup product on Cochains

The lex-projection cup product, its Leibniz rules, the structural
List-level machinery beneath them, and the physics-facing
decompositions.

## Core

  - `Core.lean` — the lex-projection cup product
  - `Ring.lean` — ring structure on H*
  - `CupOnList.lean` — cup on List-cochains
  - `CupAtomic.lean` — cup-closed cochain pair classification

## Leibniz family

  - `Leibniz.lean` — the cup-product Leibniz rule
  - `LeibnizLex.lean` / `LeibnizLexListLevel.lean` /
    `LeibnizLexStructural.lean` / `LeibnizLexSelfRef.lean` —
    twisted Leibniz for the lex cup (list-level PURE ∀k,l;
    structural lemmas; generalised self-referential form)
  - `LeibnizMirror.lean` / `LeibnizSym.lean` — reverse-lex cup +
    mirror Leibniz; symmetric cup + doubled correction
  - `LeibnizFinGeneral.lean` / `LeibnizFinPureForm.lean` —
    Fin-indexed general forms
  - `LeibnizCatalog.lean` — count-Lens recipe → δ-closure catalog
  - `LeibnizUniversal.lean` — Leibniz capstone marker

## Structural List/Fin machinery

  - `IterErase.lean` — iterated `List.eraseIdx` structural lemmas
  - `KSubsetEraseIdx.lean` / `KSubsetStructural.lean` — k-subset
    encodings
  - `SubsetIdxRoundtrip.lean` / `SubsetIdxRoundtripGeneral.lean` —
    subset-index round-trips
  - `FaceIdxGeneral.lean` / `DeltaUnfoldGeneral.lean` — face index +
    δ unfolding, general forms
  - `FinBridge.lean` / `FinBridgeGeneral.lean` — Fin bridges
  - `RangeFoldXor.lean` — `List.range`-foldl ↔ `xorRange`

## Steenrod / depth

  - `SteenrodHigherFrame.lean` — cup-1 operation framework
  - `SelfRefDepth.lean` — face-iteration depth signature

## Physics-facing

  - `InvAlphaEMDecomp.lean` — integer skeleton of 1/α_em
  - `SignedCup.lean` — signed-ℤ cup (the common α_em + CP
    infrastructure)

## Top-level

  - `Cup.lean` umbrella aggregator (one level up)
