# G150 — 메타-CD-타워: 4-Type Base × CD doubling = CD가 부분집합

**Date**: 2026-05-29
**Status**: OPEN — Phases 1-3 closed + Phase 4 ZOmegaDouble case
closed (commits `e0da617`, `38e17ad`, `620ab3c`, `0d6d9e8`,
`7d5dafa`, `0274ab3`); Phase 4 ZOmegaQuad (Hurwitz-Diophantus
polynomial) + Phases 5-6 next session(s)
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

## G150 Marathon — Phase 진행

### ✅ Phase 1 — ZOmega CommStarRing213 + IntegerNormed213 (commit `e0da617`)

`lean/E213/Lib/Math/CayleyDickson/Integer/ZOmegaAlgebra213.lean` (305줄)
신규.  ZOmega를 Algebra213 typeclass hierarchy 풀 스택 (Ring213 →
CommRing213 → StarRing213 → IntegerNormed213 → CommStarRing213
bundle) 인스턴스로 등록.  Generic `IntegerNormed213.normSq_mul`이
ZOmega의 Eisenstein 노름 multiplicativity를 typeclass 7-step calc로
자동 유도, `ZOmegaDomain`의 `quad_norm` 기반 proof 대체.

**Purity 개선**: `[propext, Quot.sound]` (quad_norm) → `[propext]` only.
Quot.sound (quotient extensionality, 무거운 axiom) 제거.

**Pattern**: ZIAlgebra213의 mirror, ω² = −1 − ω 추가 cross-term이
distributivity + mul_assoc 거쳐 propagate.  Add/Neg/Sub 인스턴스는
ZOmega.lean으로 foundational relocation.

### ✅ Phase 2 — ZOmegaDouble Ring213 via abstract bridge (commits `38e17ad`, `620ab3c`)

`ZOmegaDoubleAlgebra213.lean` (183줄) 신규.  ZOmegaDouble (concrete
struct)과 CDDouble ZOmega (abstract functor)가 구조 동일 + 연산
동일 (CD 공식 same).  Bridge `toCDDouble` + 역방향 + 5개 연산
bridge (mul, conj, add, neg, zero — 모두 rfl) 만으로 typeclass
instance transfer.

Phase 2 (`38e17ad`): `mul_assoc` 검증.
Phase 2.5 (`620ab3c`): 8개 private bridge proofs + full
`Ring213 ZOmegaDouble` + `StarRing213 ZOmegaDouble` instances.
모든 axiom이 3-line `toCDDouble_inj + rw bridges + Abstract.method`
패턴.

### ✅ Phase 3 — ZOmegaDouble IntegerNormed213 (commit `0d6d9e8`)

Type C base layer migration의 **실제 완성**.  generic
`IntegerNormed213.normSq_mul`이 ZOmegaDouble의 norm
multiplicativity를 typeclass projection으로 derive — `quad_norm`/
`hurwitz_ring` 없이.  Type A Lipschitz의 `IntegerNormed213` instance와
구조 동일 (`LipschitzHeavy.normSq_mul = IntegerNormed213.normSq_mul`)
하지만 Type C는 ZOmega base의 ω² = −1 − ω cross-term 추가 처리.

ZOmegaDouble 추가:
  · `ofInt : Int → ZOmegaDouble` + helper theorems
  · `ring_sub_zero` / `zomega_sub_zero` + `zomega_conj_neg`
  · 5개 private IntegerNormed213 field proofs (ofInt_inj',
    ofInt_add', ofInt_mul', ofInt_central', self_mul_conj')
  · `instance : IntegerNormed213 ZOmegaDouble`
  · `theorem normSq_mul` = typeclass projection (1 줄)

`ZOmegaQuadAlgebra213.lean` (87줄) 신규: bridge skeleton +
toCDDouble {_mul, _conj, _add, _neg, _zero}.  Phase 4 foundation.

### ⏳ Phase 4 — ZOmegaQuad MoufangIntegerNormed213

**Deep analysis insight (this session)**:

Computing both sides of `(uv)(v*u*) = u(vv*)u*` for `CDDouble α`
with `[IntegerNormed213 α]` base yields:

```
LHS.re - RHS.re = (cb*da - acb*d) + (a*d*bc* - d*bc*a*)
```

where a := u.re, b := u.im, c := v.re, d := v.im (all in α).

These 4-fold associative products are **not generally zero** for
arbitrary `[Ring213] [StarRing213]` non-commutative α.  The classical
Hurwitz result (octonion norms are multiplicative) relies on the
quaternion base's specific composition-algebra structure.

**Implication**: The Moufang norm-collapse identity is NOT an
abstract consequence of `IntegerNormed213` axioms alone.  It requires
additional structure on the base (composition-algebra / Hurwitz
property at the lower level).

For ZOmegaDouble specifically (= CDDouble ZOmega over commutative
Eisenstein integers), Hurwitz's theorem applies — so Moufang DOES
hold for ZOmegaQuad — but the proof requires polynomial expansion
using ZOmegaDouble's specific Hamilton-like (quaternion-analog)
identities.

**Phase 4 foundation closed** (commit `7d5dafa`):
  · `ZOmegaDouble.normSq_conj : normSq (conj u) = normSq u` —
    via typeclass: CommRing213.mul_comm bridges
    `a·conj a = ofInt(N a)` and `conj a·a = ofInt(N(conj a))`,
    then ofInt_inj.  No polynomial expansion.
  · `ZOmegaDouble.conj_mul_self : conj u · u = ofInt(normSq u)` —
    reverse-order self_mul_conj.  Derived from forward self_mul_conj
    applied to `conj u` + `conj_conj` + `normSq_conj`.

**Phase 4 ZOmegaDouble case closed** (commit `0274ab3`):
  · AlternativeNormed.lean: parametric bridges
    `[Ring213 α] → NonAssocRing213 α` +
    `[StarRing213 α] → NonAssocStarRing213 α`.
  · `instance : MoufangIntegerNormed213 ZOmegaDouble` registered.
    Moufang norm-collapse on ZOmegaDouble follows trivially from
    `Ring213.mul_assoc` (one re-association); `ofInt_paren_central`
    via mul_assoc + ofInt_central.
  · `theorem moufang_normSq_mul` witnesses generic
    `MoufangIntegerNormed213.normSq_mul` applied to ZOmegaDouble.
    `[propext]`-only.

**Phase 4 Lipschitz Type A counterpart closed** (commit `8cfa7aa`):
  · `LipschitzMoufang.lean` (61 lines) — exact mirror of
    ZOmegaDouble's Phase 4 instance.
  · `instance : MoufangIntegerNormed213 Lipschitz` via
    `Ring213.mul_assoc` (trivial).
  · `Lipschitz.moufang_normSq_mul` **strict ∅-axiom** —
    does NOT depend on propext (ZI ring axiom proofs cleaner
    than ZOmega's).

Validates MoufangIntegerNormed213 at both Type A L2 (Lipschitz)
and Type C L3 (ZOmegaDouble) associative quaternion-analog layers.
Same recipe applies at any associative `IntegerNormed213` instance
(future: Hurwitz quaternions, ZSqrt2-double, etc.).

**Remaining Phase 4 work**:

The Moufang norm-collapse identity at ZOmegaQuad —
`(u·v) · (conj v · conj u) = u · (v · conj v) · conj u` — is **not
derivable from IntegerNormed213 axioms alone**.  Both sides expand
to `ofInt(normSq(uv))` and `ofInt(normSq u · normSq v)` respectively,
so the identity is *equivalent to* `normSq_mul (uv) = normSq u ·
normSq v` at ZOmegaQuad — the very fact the typeclass machinery
aims to derive from Moufang.  Hence the proof must be **independent
polynomial computation** (Hurwitz-theorem-style).

Two paths:

(a) **Abstract**: prove `CDDouble α` Moufang norm-collapse for
    `[Ring213 α] [StarRing213 α]` parametrically in
    `AlternativeNormed.lean`.  ~100-200 lines polynomial expansion
    using base Ring213 axioms.  One-time cost, pays off across all
    CD-tower types (Cayley, Sedenion, ZOmegaQuad, ZOmegaOct,
    Hurwitz-double, …).
(b) **Concrete**: hand-prove ZOmegaQuad-specific Moufang via
    expansion in 4 ZOmegaDouble variables.  ~150 lines.  Less
    reusable.

Recommended: path (a).

Status: foundation complete, Moufang proof itself is genuine
multi-hour focused work for next session.

### ⏳ Phase 5 — SHIFT RULE 추상 functor

`shift_iso_L3` (구체 case-bash decide) 을
`[CommStarRing213 α] [CommStarRing213 β] → ...` parametric 정리로.

### ⏳ Phase 6 — Base-parametric tower constructor

`def Tower (Base : Type) [MoufangIntegerNormed213 Base] : Nat → Type`
정의 → ∀-typed tower 추상.  Type A/B/C/D 자동으로 인스턴스.

## 메타 원칙 (CLAUDE.md 보완)

> **크게 생각하고 레포지토리를 먼저 뒤져라.**
> 대부분의 직관은 코드베이스 어딘가에 이미 부분 형식화돼 있다.
> 4-row 타워 매트릭스, SHIFT RULE, Type C ZOmega tower — 모두
> 사용자가 처음 직관으로 제시한 게 이미 존재했다.

— Mingu Jeong (2026-05-29 GRA × CD 메타-타워 대화 중)
