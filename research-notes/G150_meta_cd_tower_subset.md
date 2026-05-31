# G150 — 메타-CD-타워: 4-Type Base × CD doubling = CD가 부분집합

**Date**: 2026-05-29 (trimmed 2026-05-29: closed phases promoted)
**Status**: Moufang norm-composition sub-tree **CLOSED** + promoted.
The polarization framework (`Meta/Algebra213/CDDoubleMoufang.lean`,
`CDDoubleAlternative.lean`, `Levels/SedenionZeroDivisor.lean`) and the
closed-phase journal now live in the permanent tier:

  - **Theory**: `theory/math/cayley_dickson/algebra_tower.md`
    (§"Norm composition at the octonion-analog layer") +
    essay `theory/essays/cd_tower_polarization.md`.
  - **Atlas**: `theory/essays/tower_atlas.md` (CD tower as one Lens
    reading of the P-orbit; boundary vs other repo "towers").
  - **Session journal**: `HANDOFF.md` (Phase 1–4 commit history,
    flexibility cross-pair scoping).

This note now holds only the **still-open scratch** (Phase 5–6) plus
the originating observation.

## 핵심 관찰 (originating insight)

> "타워를 올라가는게 Raw의 2페어나 3페어를 하는거자나 (1, w, w^2,
>  이것도 있음). 이렇게 타고 올라가다 보면 cd 곱셈의 레이어들과
>  만나는 지점도 있을거니깐, cd 타워가 이 타워의 부분집합인거 같아서"
> — Mingu Jeong 2026-05-29

고전 Cayley-Dickson tower = **Type A 단일 column**.
메타 타워 = (Type 선택 × CD doubling layer) 매트릭스.
SHIFT RULE = 매트릭스 cell 간 isomorphism.

## 4 Type × CD doubling matrix

| Type | Base | atom 구조 | 사용자 매핑 |
|---|---|---|---|
| **A** | ZI = ℤ[i] | (1, i) 2-pair | "2페어" |
| **B** | ZSqrt[D≥2] = ℤ[√D] | (1, √D) 2-pair w/ D-twist | "2페어 변형" |
| **C** | ZOmega = ℤ[ω], ω²+ω+1=0 | **(1, ω, ω²)** 3-element | **"(1,w,w²)" — 정확 일치** |
| **D** | Hurwitz | modified quaternion | quaternion 변형 |

```
Type A:  ZI → Lipschitz → Cayley → Sedenion → Trigintaduonion → Pathion
           2      4         8        16          32              64
Type B:  ZSqrt → L3T → L4T → L5T → L6T → L7T → L8T → L9T
                 2     4     8     16    32    64    128   256
Type C:  ZOmega → ZOmegaDouble → ZOmegaQuad → ZOmegaOct
           2          4              8           16
Type D:  Hurwitz → HurwitzL2 → HurwitzL3   (24 → 48 → 96 units)
```

Type E는 reject (`Misc/TypeE_Rejection.lean`) — 4-row가 complete 진술.
dimension은 layer마다 ×2 (CD doubling).

## SHIFT RULE — 타워 간 만남점 (concrete cases closed)

`ZSqrtMinus2Findings.shift_iso_L3`: ZI units (Type A L2, 4 원소) ≅
L3T units (Type B L3, 4 원소) at unit-loop level — 다른 Type, layer가
1 다른데 구조 동일.  `SedenionOrder4Monopoly`: Type A L5 ≅ Type B L6
(order distribution `{1, 1, 30}` 일치).
→ 사용자 직관 "cd 곱셈의 레이어들과 만나는 지점" = SHIFT RULE 좌표.

## 무엇이 누락? — Parametric meta-framework

| 있는 것 | 없는 것 |
|---|---|
| 4 Type 각각 구체 형식화 | 하나의 parametric framework |
| SHIFT RULE 구체 case (`shift_iso_L3`) | SHIFT RULE 추상 functor 진술 |
| `TowerFixedPoint.lean` (3 fates) | base-parametric tower constructor |
| `MoufangIntegerNormed213` (closed) | tower 구성을 typeclass argument로 받는 인터페이스 |

곱셈 구조 (cross-term bilinear, conjugation)는 모두 Lens 밖
(algebra-side); Algebra213 typeclass가 그 빈 공간을 메운다.

## ⏳ OPEN — next-session targets

### Phase 5 — SHIFT RULE 추상 functor
`shift_iso_L3` (구체 case-bash decide) 을
`[CommStarRing213 α] [CommStarRing213 β] → ...` parametric 정리로.

### Phase 6 — Base-parametric tower constructor
`def Tower (Base : Type) [MoufangIntegerNormed213 Base] : Nat → Type`
정의 → ∀-typed tower 추상.  Type A/B/C/D 자동으로 인스턴스.

### (math crux) Flexibility over a non-associative base
`Meta/Algebra213/CDDoubleFlexible.lean` foundation PURE; remaining
cross-pair identity scoped in `HANDOFF.md` + `algebra_tower.md`
§"Open frontier" #2.

## 메타 원칙 (CLAUDE.md 보완)

> **크게 생각하고 레포지토리를 먼저 뒤져라.**
> 대부분의 직관은 코드베이스 어딘가에 이미 부분 형식화돼 있다.
> 4-row 타워 매트릭스, SHIFT RULE, Type C ZOmega tower — 모두
> 사용자가 처음 직관으로 제시한 게 이미 존재했다.

— Mingu Jeong (2026-05-29 GRA × CD 메타-타워 대화 중)
