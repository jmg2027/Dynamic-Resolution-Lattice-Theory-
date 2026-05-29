# G150 — 메타-CD-타워: 4-Type Base × CD doubling = CD가 부분집합

**Date**: 2026-05-29
**Status**: OPEN (insight 정리, 일부 형식화 가능성 조사)
**Lean (existing)**:
  - `E213.Lib.Math.CayleyDickson.Integer.{ZI,ZOmega,ZSqrt,Hurwitz213}` (4 base)
  - `E213.Lib.Math.CayleyDickson.Levels.{Cayley,Sedenion,...}` (Type A)
  - `E213.Lib.Math.CayleyDickson.Integer.ZOmega{Double,Quad,Oct}` (Type C)
  - `E213.Lib.Math.CayleyDickson.Integer.{ZSqrtMinus2Tower,Order4Monopoly_L*T}` (Type B)
  - `E213.Lib.Math.CayleyDickson.Integer.ZSqrtMinus2Findings.shift_iso_L3` (SHIFT RULE 구체 case)
  - `E213.Meta.Algebra213.AlternativeNormed.MoufangIntegerNormed213` (이번 추가, abstract layer)
**Narrative (existing)**: `theory/math/cayley_dickson/algebra_tower.md` §"4-row matrix"

## 핵심 관찰

> "타워를 올라가는게 Raw의 2페어나 3페어를 하는거자나 (1, w, w^2,
>  이것도 있음). 이렇게 타고 올라가다 보면 cd 곱셈의 레이어들과
>  만나는 지점도 있을거니깐, cd 타워가 이 타워의 부분집합인거 같아서"
> — Mingu Jeong 2026-05-29

이 직관이 정확히 맞고, 코드베이스에 이미 **4-row 타워 매트릭스**가
부분 형식화돼 있다.

## 4 Type × Layer matrix (`algebra_tower.md` :132-154)

| Type | Base | atom 구조 | 사용자 매핑 |
|---|---|---|---|
| **A** | ZI = ℤ[i] | (1, i) 2-pair | "2페어" |
| **B** | ZSqrt[D≥2] = ℤ[√D] | (1, √D) 2-pair w/ D-twist | "2페어 변형" |
| **C** | ZOmega = ℤ[ω], ω²+ω+1=0 | **(1, ω, ω²)** 3-element | **"(1,w,w²) 이것도 있음" — 정확 일치** |
| **D** | Hurwitz | modified quaternion | quaternion 변형 |

Type E는 명시적으로 reject (`Misc/TypeE_Rejection.lean`) — 4-row가
완전(complete) 형식 진술.

## 각 Type 위 CD doubling tower

```
Type A:   ZI → Lipschitz → Cayley → Sedenion → Trigintaduonion → Pathion
            2      4         8        16          32              64
Type B:   ZSqrt → L3T → L4T → L5T → L6T → ...
                  2     4     8     16    32
Type C:   ZOmega → ZOmegaDouble → ZOmegaQuad → ZOmegaOct → ...
            2          4              8           16
Type D:   Hurwitz (base)
```

dimension은 layer마다 ×2 (CD doubling). 사용자 표현 "올라갈수록 한 수를
더 많은 N으로 표현해야" 정확.

## SHIFT RULE — 타워 간 만남점

`ZSqrtMinus2Findings.lean:53-54`:

```lean
theorem shift_iso_L3 :
    ∀ a ∈ ZIUnits, ∀ b ∈ ZIUnits,
        φ (ZI.mul a b) = φ a * φ b := by decide
```

ZI units (Type A L2, 4 원소) ≅ L3T units (Type B L3, 4 원소) at
unit-loop level. **다른 Type, layer가 1 다른데 구조 동일**.

`SedenionOrder4Monopoly.lean:15`: Type A L5 ≅ Type B L6 (order
distribution `{1, 1, 30}` 일치).

→ 사용자 직관 "cd 곱셈의 레이어들과 만나는 지점" = SHIFT RULE 좌표.

## "CD 타워는 이 메타 타워의 부분집합" — 정확

고전 Cayley-Dickson tower = Type A 단일 column.  
메타 타워 = (Type 선택 × CD doubling layer) 매트릭스.  
SHIFT RULE = 매트릭스 cell 간 isomorphism.

## Raw 기반 emergence 측면

각 base type의 carrier만은 Raw lens view로 표현 가능 (single binary
op이 commutative + associative한 부분):

| Base | Raw lens 표현 가능성 |
|---|---|
| ZI | `signedLens` (ℤ) × 2-pair → ℤ²; 곱셈은 algebra-side |
| ZOmega | 3-pair lens `Lens (ℕ × ℕ × ℕ)` + ω 관계로 quotient |
| ZSqrt[D] | 2-pair lens + √D-graded add |
| Hurwitz | quaternion grading |

**곱셈 구조 (cross-term bilinear, conjugation)**은 모두 Lens 밖
(algebra-side). Algebra213 typeclass가 그 빈 공간을 메움.

## 무엇이 누락? — Parametric meta-framework

| 있는 것 | 없는 것 |
|---|---|
| 4 Type 각각 구체 형식화 | 하나의 parametric framework |
| SHIFT RULE 구체 case (`shift_iso_L3`) | SHIFT RULE 추상 functor 진술 |
| `TowerFixedPoint.lean` (3 fates) | base-parametric tower constructor |
| `MoufangIntegerNormed213` (이번 추가) | tower 구성을 typeclass argument로 받는 인터페이스 |

## 자연스러운 다음 행보

1. **Type C 기반: ZOmega PURE typeclass 인스턴스** (이 세션에서 시도 →
   blocker 발견, 차회 target).  ZOmega를 `CommStarRing213` 인스턴스로
   등록하려면 ZOmega의 ring axiom들이 ∅-axiom 으로 필요한데,
   현재 `ZOmegaDomain.normSq_mul`은 `quad_norm` 태틱으로 증명돼 있고
   `quad_norm`은 DIRTY (`propext, Quot.sound`).  `mul_assoc` 도 같은
   상황 예상.  → **ZIAlgebra213가 ZI를 PURE 화한 패턴 (componentwise
   Int213 projection) 그대로 ZOmega 에 복제 필요**.  ZOmega 곱셈이
   ZI 보다 cross-term 1 개 더 (ω² = −1−ω 보정), 분량 ~120-150줄
   예상.
2. **이후 ZOmegaDouble Ring213 + IntegerNormed213**: ZOmega가 PURE
   commutative star ring 이 되면, `instRing213CDDouble` (CommStarRing213
   base → Ring213 (CDDouble α)) 으로 ZOmegaDouble 자동 Ring213.
   단 ZOmegaDouble 구조가 `structure { re : ZOmega, im : ZOmega }` 라
   `CDDouble ZOmega` 와 isomorphic 한 bridge instance 필요.
3. **ZOmegaQuad MoufangIntegerNormed213**: ZOmegaDouble (associative
   non-comm) → ZOmegaQuad (alternative non-assoc) 단계.  이번
   세션 추가한 `MoufangIntegerNormed213` 의 generic `normSq_mul` 적용
   first test point.
4. **SHIFT RULE 추상 functor**: `shift_iso_L3` (구체 case-bash decide)
   을 `[CommStarRing213 α] [CommStarRing213 β] → ...` parametric 정리로.
5. **Base-parametric tower constructor**:
   `def Tower (Base : Type) [MoufangIntegerNormed213 Base] : Nat → Type`
   정의 → ∀-typed tower 추상.  Type A/B/C 가 자동으로 인스턴스.

## 메타 원칙 (CLAUDE.md 보완)

> **크게 생각하고 레포지토리를 먼저 뒤져라.**
> 대부분의 직관은 코드베이스 어딘가에 이미 부분 형식화돼 있다.
> 4-row 타워 매트릭스, SHIFT RULE, Type C ZOmega tower — 모두
> 사용자가 처음 직관으로 제시한 게 이미 존재했다.

— Mingu Jeong (2026-05-29 GRA × CD 메타-타워 대화 중)
