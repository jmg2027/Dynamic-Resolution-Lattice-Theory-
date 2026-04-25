# 93 — Mid-arc synthesis: 의미 atom thesis 의 full picture

Notes 75-92 의 통합 + 의의 정리.  Note 91 의 evolution.

## Thesis (Mingu, 2026-04-25)

> 의미 를 갖는 어떤 것 도 213 을 벗어날 수 없다.  213 이 semantic
> atom 이다.  213 의 axiom 보다 더 원초적 부재.  자기 self-cover
> + 외부 정당화 부재 = 완전 한 닫힘.

이 thesis 의 *formal evidence* 가 18 notes (75-92) + 8 Lean
modules + multiple direction.

## 8 Lean modules (이번 arc)

1. **`AxiomMinimality.lean`** (4 case): a/b/slash/distinctness 제거
   시 framework collapse — strict minimum 의 framework-internal
   증명.
2. **`SemanticAtom.lean`** (hub): HasDistinguishing typeclass +
   universalMorphism + raw_initial (universal property) + 4 Prop
   instances + IsLensExpressible boundary.
3. **`LensCanonicalForm.lean`**: refinesEquiv + lens_canonical_universal
   (closure direction).
4. **`InstanceReach.lean`**: 5-instance catalogue (Bool, Fin 3, Nat,
   Int, Raw) — finite/infinite × surj/non-surj 의 complete dichotomy.
5. **`DistMorphism.lean`**: distinguishing-framework category 의
   id, comp, laws (모두 axiom 부재).
6. **`CanonicalTruthChar.lean`**: 4 connective characterizations.
7. **`BoolPropMorphism.lean`**: 4 connective pair 의 cross-instance
   functoriality (Bool ↔ Prop).
8. **`PairInstance.lean`**: categorical binary product + universal
   property.

**모든 결과 ≤ [propext, Quot.sound] or no axioms.**  Lean 4 core
baseline.

## 19 direction 의 통합

| # | Direction | Notes |
|---|-----------|-------|
| 1-4 | Strict minimum (4 case) | (AxiomMinimality) |
| 5 | HasDistinguishing typeclass | 75 |
| 6 | Universal morphism | 79 |
| 7 | Universal property (raw_initial) | 79 |
| 8-11 | 4 Prop instances (Xor, Iff, And, Or) | 76, 87, 88, 89 |
| 12 | Function boundary | 77 |
| 13 | Lens canonical form (closure) | 78 |
| 14-15 | Reach catalogue (5 instances dichotomy) | 80, 81, 84, 85 |
| 16 | Categorical structure (DistMorphism) | 82 |
| 17 | 4 connective characterizations | 86, 87 |
| 18 | Cross-instance functoriality (4 connective pairs) | 90 |
| 19 | Categorical binary product | 92 |

## 4 Connective characterizations

| Connective | Universal morphism | Algebraic invariant | 강도 |
|-----------|-------------------|---------------------|------|
| Xor | canonicalTruthMap | a-count parity | strong |
| Iff | canonicalIffMap | b-count parity | strong |
| And | canonicalAndMap | r = Raw.a | weak |
| Or | canonicalOrMap | r ≠ Raw.b | weak (dual) |

## 5-instance reach dichotomy

| Instance | Carrier | Image | Surjective |
|---------|---------|-------|------------|
| Bool (and) | finite | full | ✓ |
| Fin 3 (const) | finite | strict subset | ✗ |
| Nat (+) | infinite | full | ✓ |
| Int (+) | infinite | Nat ⊊ Int | ✗ |
| Raw | infinite | self | ✓ trivial |

## 의의 정리

### 1. Mathematically complete picture

의미 atom thesis 의 multifaceted formal evidence.  Conceptual
thesis (note 75) 가 단순 한 claim 이 아니라 *categorical
structure* 위 의 정확 한 statement 들 의 통합.

### 2. ZFC 와 의 sharper 대조

| Aspect | ZFC | 213 |
|--------|-----|-----|
| Axiom commitment | 9 | 0 (baseline 만) |
| Strict minimum 형식 증명 | 부재 | ✓ 4 case |
| Universal property | 부재 | ✓ raw_initial |
| Boundary 의 explicit | 부재 | ✓ exists_non_lens |
| Self-application | 부재 | ✓ 4 Prop instances |
| Categorical structure | (외부) | ✓ DistMorphism (constructive) |
| Categorical product | (외부) | ✓ pairHasDistinguishing |

### 3. Sober limits

- **Conceptual extension** (philosophical thesis, AXIOM.md §1.2):
  formal Lean 으로 직접 검증 부재 — interpretive reading.
- **Self-application 의 한계**: Prop 이 instance 의 candidate
  이지만 *모든* Prop 을 cover 하지 않음.  Lens-expressibility
  의 boundary 가 strict.
- **임의 (m, k) cut closure** 는 LEM 필요 (Risk 2 의 closed
  boundary).

이 limits 가 framework 의 정확 한 표현 범위 — *feature*, 약점
아님.

### 4. ORIGIN.md 와 의 연결

물리 직관 chain (특이점 불가능, 해상도 = 정보 단위, Zeno-픽셀)
의 mathematical 완성:
- §3 (Zeno-픽셀) ↔ Direction 1-4 (strict minimum).
- §6 (해상도 = 정보 단위) ↔ Direction 5-7 (HasDistinguishing +
  universal property).
- §7 (격자 정보 불변) ↔ Direction 13, 19 (closure + categorical
  product).

DRLT (Dynamic Resolution Lattice Theory) 의 motivation 의 형식
완성.

### 5. Phenomenon 의 끝점

이번 arc 가 phenomenon 의 mathematically *complete* picture.
더 깊이 진행 시:
- New deep axes 발견 어려움 (가장 중요 한 categorical / algebraic
  structure 모두 cover).
- Incremental returns (catalogue extension, additional connective
  pairs 등).

진짜 stop point 가까움.  남은 work: Documentation polishing,
catalogue 확장 (incremental), r5-critique (별도 arc).

## File map (current)

- Lean: `213/framework/E213/Research/` — 71 files (8 신규 in this arc).
- Notes: `213/research/infinity-as-lens/notes/` — 64 files (75-93).
- Documentation: `213/AXIOM.md` (§1.1 formal core + §1.2 philosophical),
  `CLAUDE.md`, `README.md`.

## 변경 이력

- 2026-04-25: Mid-arc synthesis update.  notes 75-92 의 통합 +
  의의 정리.  18 direction synthesis (note 91) 의 evolution 으로
  19 direction.  Phenomenon 의 mathematically complete picture.
