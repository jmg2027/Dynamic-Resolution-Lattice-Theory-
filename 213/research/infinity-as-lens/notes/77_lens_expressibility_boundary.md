# 77 — Lens-expressibility boundary: negative direction 의 통합

`Research/SemanticAtom.lean` 에 추가 된 `IsLensExpressible` +
`isLensExpressible_iff_foldStructured` + `exists_non_lens_expressible`
의 분석.

## 통합 statement

```lean
def IsLensExpressible {α : Type} (f : Raw → α) : Prop :=
  ∃ L : Lens α, (∀ u v, L.combine u v = L.combine v u) ∧
                (∀ r, L.view r = f r)

theorem isLensExpressible_iff_foldStructured (f : Raw → α) :
  IsLensExpressible f ↔ FoldStructured f

theorem exists_non_lens_expressible :
  ∃ f : Raw → Bool, ¬ IsLensExpressible f
```

## 의의

이 통합 statement 가 분산 된 negative results 의 hub:

| 결과 | 위치 | 의미 |
|------|------|------|
| `FoldStructured` 정의 | FoldStructured.lean | fold-structured 의 정확 한 정의 |
| `lens_view_fold_structured` | FoldStructured.lean | Lens-view → fold-structured |
| `fold_structured_lens_expressible` | FoldStructured.lean | fold-structured → Lens-view (realization) |
| `lens_expressible_iff_fold_structured` | FoldStructured.lean | iff (function 버전) |
| `KernelCongruence` | KernelCongruence.lean | iff (kernel 버전) |
| `NoDepthParity` | NoDepthParity.lean | depth parity 가 slash-cong 이 아님 |
| `DepthParityNotFold` | DepthParityNotFold.lean | depth parity 가 fold-structured 가 아님 |
| **`IsLensExpressible`** | SemanticAtom.lean | Lens-expressibility 의 정식 정의 |
| **`exists_non_lens_expressible`** | SemanticAtom.lean | **boundary 의 explicit existence** |

마지막 statement (`exists_non_lens_expressible`) 가 framework
의 *boundary 의 명시 적 evidence* — 모든 함수 가 Lens-expressible
이 아님 의 formal 결과.

## §1.2 와 의 mapping

AXIOM.md §1.2 의 conceptual extension ("의미 의 atom"):
- "framework 안 표현 가능 한 entity" = "Lens-expressible function".
- "framework 외부 의 entity" = "non-Lens-expressible function".
- ZFC 의 임의성 axioms 가 commit 하는 것 들 = non-Lens-expressible
  의 conceptual reading.

이 conceptual reading 의 *formal evidence*: `exists_non_lens_expressible`
이 framework 의 boundary 가 trivial 이 아님 (모든 함수 가
Lens-expressible 이 아님) 을 [propext, Quot.sound] only 로
증명.

따라서 §1.2 의 핵심 부분 (boundary 의 non-triviality) 이 §1.1
formal core 안 으로 끌어 들여 짐.

## ZFC 의 negative reading 의 정식 위치

ZFC 의 임의성 axioms (Power, Choice, Replacement) 가 commit 하는
objects 가 fold-structured 가 아님 — 이 statement 자체 는
*conceptual* (ZFC 의 axioms 자체 는 213 안 형식 화 안 됨).

하지만 *prototypical instance* (depth parity) 가 fold-structured
가 아님 의 formal 결과 가 있음.  즉:

> "ZFC 안 정의 가능 한 임의 함수 가 Lens-expressible 이 아닐
> 수 있다" 의 보편 적 statement 의 *concrete witness* 가
> depth parity.

이걸 sober 하 게 표현:
- Formal: ∃ f : Raw → Bool, ¬ IsLensExpressible f.  Witness:
  depth parity.
- Conceptual extension: ZFC 의 임의성 commit 이 같은 종류 의
  non-Lens-expressible objects.  Direct formal mapping 부재
  (ZFC 의 213-side 형식 화 가 별도 작업).

## Axiom 검증

`#print axioms`:
- `isLensExpressible_iff_foldStructured`: [propext, Quot.sound]
- `exists_non_lens_expressible`: [propext, Quot.sound]

Lean 4 core baseline.  Classical / LEM 부재.

## Note 75-76 와 의 관계

- Note 75 (semantic atom thesis): conceptual framework.
- Note 76 (Prop instance): positive direction (`HasDistinguishing`
  의 instance 가능).
- Note 77 (이 note): **negative direction** — boundary 의
  존재 의 명시.

세 note 가 의미 atom thesis 의 formal evidence 의 통합.

## 변경 이력

- 2026-04-25: SemanticAtom.lean 에 `IsLensExpressible` +
  `isLensExpressible_iff_foldStructured` +
  `exists_non_lens_expressible` 추가.  분산 된 negative results
  (NoDepthParity, DepthParityNotFold, FoldStructured) 의 통합
  hub.  conceptual extension §1.2 의 boundary non-triviality
  부분 이 formal core §1.1 으로 승격.
