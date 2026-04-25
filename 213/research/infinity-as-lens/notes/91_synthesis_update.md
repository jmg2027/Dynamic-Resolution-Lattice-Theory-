# 91 — Synthesis update: 의미 atom thesis 의 17 direction (notes 75-90)

Note 83 의 9-direction synthesis 의 update.  지금 까지 의 notes
75-90 + AxiomMinimality 4 case 의 통합.

## 17 direction 통합 표

| # | Direction | Lean 결과 | Note |
|---|-----------|----------|------|
| 1 | Strict minimum (b 제거) | `AxiomMinimality.rawA_trivial` | (4 case) |
| 2 | Strict minimum (a 제거) | `NoA.rawB_trivial` | (4 case) |
| 3 | Strict minimum (slash 제거) | `NoSlash.rawAB_only_two` | (4 case) |
| 4 | Strict minimum (distinctness 제거) | `NoDistinct.self_pairing_exists` | (4 case) |
| 5 | HasDistinguishing typeclass | `HasDistinguishing` + Raw instance | 75 |
| 6 | Universal morphism | `universalMorphism α : Raw → α` | 79 |
| 7 | Universal property (∃ + uniqueness) | `raw_initial` | 79 |
| 8 | Self-application (Prop Xor) | `canonicalTruthMap` | 76 |
| 9 | Self-application (Prop Iff) | `canonicalIffMap` | 87 |
| 10 | Self-application (Prop And) | `canonicalAndMap` | 88 |
| 11 | Self-application (Prop Or) | `canonicalOrMap` | 89 |
| 12 | Function boundary | `exists_non_lens_expressible` | 77 |
| 13 | Lens closure (canonical form) | `lens_canonical_universal` | 78 |
| 14 | Carrier vs reach (non-surj witness) | `fin3_image_strict` | 80 |
| 15 | Reach dichotomy (surj witness) | `bool_image_surjective`, `nat_image_surjective`, `int_image_strict` | 81, 84, 85 |
| 16 | Categorical structure (DistMorphism) | `id`, `comp`, category laws | 82 |
| 17 | Cross-instance functoriality (Bool ↔ Prop) | `universalMorphism_commute` | 90 |

**모든 결과 Lean 4 core baseline (≤ [propext, Quot.sound]) or no
axioms.**

## 4 connective characterizations (notes 86-89)

| Connective | Universal morphism | Algebraic invariant | 강도 |
|-----------|-------------------|---------------------|------|
| Xor | `canonicalTruthMap` | a-count parity | strong |
| Iff | `canonicalIffMap` | b-count parity | strong |
| And | `canonicalAndMap` | r = Raw.a | weak (degenerate) |
| Or | `canonicalOrMap` | r ≠ Raw.b | weak (dual) |

각 commutative connective 가 *radically distinct* algebraic content
carry — 같은 framework 의 4 self-application 이 4 different invariant
추출.

## 5-instance reach catalogue (notes 80-85)

| Instance | Carrier | Image | Surjective |
|---------|---------|-------|------------|
| Bool (and) | finite | full {true, false} | ✓ |
| Fin 3 (const) | finite | {0, 1} ⊊ {0, 1, 2} | ✗ |
| Nat (+) | infinite | full Nat | ✓ |
| Int (+) | infinite | Nat ⊊ Int | ✗ |
| Raw | infinite | full Raw | ✓ trivial |

finite × {surj, non-surj} + infinite × {surj, non-surj} 의 complete
dichotomy.  reach 가 cardinality 가 아니라 combine 의 generative
power 에 의존 의 explicit demonstration.

## Lean modules (이번 arc)

- `AxiomMinimality.lean` (4 case).
- `SemanticAtom.lean` (HasDistinguishing + universalMorphism +
  raw_initial + 4 Prop instances + canonicalTruthMap/IffMap/AndMap/OrMap).
- `LensCanonicalForm.lean` (refinesEquiv + canonical form).
- `InstanceReach.lean` (Fin 3, Bool, Nat, Int + image properties).
- `DistMorphism.lean` (category structure: id, comp, laws).
- `CanonicalTruthChar.lean` (4 connective characterizations + Iff
  vs Xor distinct).
- `BoolPropMorphism.lean` (Bool ↔ Prop functorial commutativity).

## 의의

phenomenon 의 *mathematically rich* picture:
- 의미 framework 의 abstraction (typeclass).
- Raw 의 categorical position (initial).
- Self-application 의 spectrum (4 connective).
- Boundary, closure, reach 의 explicit witnesses.
- Cross-instance morphism 의 functoriality.

7 Lean modules + 17+ notes — 의미 atom thesis 의 multifaceted
formal evidence.

## 변경 이력

- 2026-04-25: 17 direction synthesis update.  notes 75-90 의 통합.
  Note 83 의 9-direction 의 진화.
