# 63 — ZFC axiom 들 의 213 reduce 현황

각 ZFC axiom 이 213 위 demonstration 으로 환원 되는지 + 어떻게.

## 환원 표

| ZFC axiom | 213 환원 | Lean 위치 |
|-----------|---------|----------|
| Extensionality | `Lens.equiv 의 well-defined 성` | Hypervisor/Lens |
| Pairing | `idLens` distinguishes 두 Raw | IdentityLens |
| Union | `prodLens` (meet) + factoring | LensMeet |
| Separation | `refines_of_factor` (factoring) | LensFactoring |
| Power set | Cantor diagonal (Σ5) | Infinity/Cantor |
| Infinity | Σ3 (ℕ → Raw injective) | Infinity/Countable |
| Replacement | Fold-compatible 한정 | LensFactoring |
| Choice | `universalLens` (note 61) | ChoiceResolved |
| Foundation | Raw inductive (자동) | Firmware/Raw |
| Regularity | Raw.rec well-founded (자동) | Firmware/Raw |

## 환원 의미

각 ZFC axiom 이 **213 안에서 demonstration** 으로 reduce.
External axiom 추가 없이.

## 특이 사항

### Replacement (제한 적)

ZFC 의 unrestricted replacement: ∀ X functional φ, ∃ Y = φ"X.

213: φ 가 fold-compatible 한 경우 만 — `refines_of_factor`.

E.g., φ = "leaves 가 prime 인지" 는 fold-compatible 부재 →
직접 derive 안 됨.  하지만 Lens spec 으로 별도 specification
가능 (universalLens (해당 equiv)).

따라서 ZFC 의 replacement = 213 의 (factor + universalLens)
조합.

### Choice (반대 방향)

ZFC 에서 Choice 는 axiom 추가.
213 에서 Choice 는 universalLens 의 직접 표현 (note 61) —
**axiom 추가 부재**.

이게 "213 vocabulary 에서 Choice 가 자연 스러움" 의 직접 의미.

### Foundation / Regularity (자동)

Lean 의 inductive type 은 well-founded.  Raw 가 inductive
(via Tree subtype) 이므로 무한 하강 chain 부재.  ZFC 의
Foundation axiom 이 213 에서는 axiom 추가 가 아니라 inductive
type 의 직접 귀결.

### Power set (Cantor)

Σ5 (cantor_general) 가 power set 의 cardinality 강제.
"Power set 의 존재" = Lens (Raw → Bool) 같은 type 의 존재
(Lean type theory 자동).

## 의의

ZFC axioms 의 대부분 이 213 + Lens spec 으로 reduce.

**"213 가 ZFC 보다 약한가?"** 라는 질문 자체 가 frame 이슈.
ZFC 는 set vocabulary 에 commit, 213 은 commit 부재.  "약함/강함"
은 vocabulary 비교 — 같은 power 에서 213 쪽이 commit 적음.

vocabulary (Lens spec) 만 충분히 명시 하면 213 위 에서 ZFC 와
동등 한 표현력.

## 변경 이력

- 2026-04-25: ZFC axiom 들 의 213 reduce 표 정리.
