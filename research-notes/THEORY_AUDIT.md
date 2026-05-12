# Theory/ Layer Character Audit

**Audit date**: 2026-05-12 (post-Phase-3 Theory→Term split,
post-ARCHITECTURE.md 4 ring + Meta rewrite).

**Subject**: `lean/E213/Theory/` — 48 .lean files, 8 sub-clusters.

**Reference**: `lean/E213/ARCHITECTURE.md` (canonical layer spec
2026-05-12).  Each ring may use: itself + immediate-below ring's
API + Meta.

## 0. Summary

| Cluster | Files | Lines | Spec status |
|---|---|---|---|
| `Theory/Raw/`        | 11 |  961 | ✓ except `Mobius.lean` |
| `Theory/Atomicity/`  |  8 |  764 | ✓ except `ArityForcingGeneral.lean` |
| `Theory/Internal/`   |  6 | 2026 | ✓ (all clean) |
| `Theory/Nat213/`     |  6 | 1119 | 3 violations (AlgebraicGeometry, AtomicityCorrespondence, RotationGeometry) |
| `Theory/Closed/`     |  7 | 1603 | ✓ except `Nat213Bridge.lean` |
| `Theory/Tower/`      |  3 |  374 | ✓ (all clean) |
| `Theory/CDDouble/`   |  3 |  171 | ✓ except `UniversalInduction.lean` |
| `Theory/Tools/`      |  1 |  153 | ✗ `CertChecker.lean` |
| `Theory/*.lean`      |  3 |  ~80 | ✓ (aggregators API/Atomicity/Raw) |

**Total**: 48 files, **8 ring-violations** (Theory → Lib import).
No Theory → Lens or Theory → App violations.

## 1. Per-cluster character

### 1.1 `Theory/Raw/` — Raw axiom 공개 표면 (11 files)

Raw의 axiom commitment (a, b, slash, slash_comm) + 구조적 정리.

| File | Lines | Role | Spec |
|---|---|---|---|
| Core.lean      | 30 | Raw subtype + DecidableEq + a, b | ✓ Term API only |
| Slash.lean     | ?  | Raw.slash smart constructor + slash_comm | ✓ |
| Fold.lean      | ?  | Raw.fold catamorphism | ✓ |
| Swap.lean      | ?  | a ↔ b automorphism | ✓ |
| SwapSlash.lean | ?  | swap + slash 호환 | ✓ |
| Levels.lean    | ?  | depth-leaves 관찰 | ✓ |
| Hom.lean       | ?  | fold homomorphism | ✓ |
| Rec.lean       | ?  | custom eliminator | ✓ |
| Signed.lean    | ?  | signed lens bridge (Int213 internal) | ✓ |
| Demo.lean      | ?  | examples | ✓ |
| **Mobius.lean** | 78 | Möbius matrix bridge | ✗ → `Lib.Math.Tactic.Ring213` |

성격: Term API (Tree machinery) 위 Raw axiom 의 공개 표면.
**Mobius.lean** 만 Ring 위반 — Möbius matrix [[2,1],[1,1]] 의
Pell-Fib recurrence 증명에 Ring213 tactic 사용.

### 1.2 `Theory/Atomicity/` — forced-shape uniqueness (8 files)

`(NS, NT, d) = (3, 2, 5)` 이 forced 임을 pure-ℕ 로 증명 (Raw 의존
zero).

| File | Lines | Role | Spec |
|---|---|---|---|
| Alive.lean              | ?  | sub-property | ✓ |
| Five.lean               | ?  | atomic_iff_five | ✓ Meta.Tactic only |
| FiveHelpers.lean        | ?  | Five 보조 | ✓ |
| PairForcing.lean        | ?  | (NS, NT, d) unique | ✓ |
| NonDecomposable.lean    | ?  | sub-property | ✓ |
| PrimitiveSizes.lean     | ?  | 작은 size 제거 | ✓ |
| ArityForcing.lean       | ?  | arity=2 forced | ✓ |
| **ArityForcingGeneral.lean** | 98 | 일반 arity 제거 | ✗ → `Lib.Math.Pigeonhole` |

성격: "Raw axiom 이 존재한다면 그 shape 은 (3,2,5) 이다" 의
pure-ℕ 메타정리.  Raw import 0.  **ArityForcingGeneral** 만
Pigeonhole 사용 — 일반 arity n 의 ruling-out 에 필요.

### 1.3 `Theory/Internal/` — implementation detail (6 files)

| File | Lines | Role | Spec |
|---|---|---|---|
| RawCmpIndependence.lean      | ?  | cmp choice 가 axiom-외 | ✓ |
| Int213.lean                  | ?  | ℤ 의 213-helpers | ✓ |
| Int213Instance.lean          | ?  | Int213 instances | ✓ |
| Algebra213.lean              | ?  | algebra 기저 | ✓ |
| Algebra213CDDouble.lean      | ?  | CD doubling 기저 | ✓ |
| Algebra213CDDoubleStar.lean  | ?  | CD doubling 확장 | ✓ |

성격: Internal — direct import 외부 권장 안 됨.  RawCmpIndependence
는 axiom-encoding-independence meta-theorem.  Int213/Algebra213
계열은 algebra tower 의 internal building blocks.

전부 spec 정합 — Lib import 없음, namespace `E213.Theory.Internal`
유지.

### 1.4 `Theory/Nat213/` — inductive Layer 2 Nat + 응용 (6 files)

| File | Lines | Role | Spec |
|---|---|---|---|
| Core.lean                       | ?  | `inductive Nat213 \| one \| succ` + add/mul | ✓ |
| Lenses.lean                     | ?  | Raw → Nat213 lens family | ✓ |
| **AtomicityCorrespondence.lean** | 56 | (NS,NT,d) ↔ ctor count | ✗ → 2× Lib |
| OneAsGlue.lean                  | ?  | "1" 의 의미 | ✓ (간접 Mobius via Raw) |
| **RotationGeometry.lean**       | 259 | 회전 기하 | ✗ → `Lib.Math.Topology.EulerChi` |
| **AlgebraicGeometry.lean**      | 186 | algebraic geometry | ✗ → 2× Lib (EulerChi, Hurwitz213) |

성격: Layer 2 standalone inductive (Raw 무관) + 그 위 Lens
characterization + 기하/대수 응용.  Core/Lenses 는 spec 정합.
나머지 3 응용 파일은 Lib import — Lib 콘텐츠 성격.

### 1.5 `Theory/Closed/` — Method A Raw chain (7 files)

| File | Lines | Role | Spec |
|---|---|---|---|
| FoldRaw.lean              | ?  | Raw → Raw fold | ✓ |
| Bool213.lean              | ?  | Raw → Bool projection | ✓ |
| Bool213System.lean        | ?  | Bool projection system | ✓ |
| Nat213.lean               | ?  | Layer 1 chain (one := Raw.a) | ✓ |
| **Nat213Bridge.lean**     | 415 | Layer 1 ↔ Layer 2 동형성 | ✗ → `Lib.Math.NatHelpers.PureNat` |
| NumberingSystem.lean      | ?  | numeral encoding | ✓ |
| RawCut.lean               | ?  | Raw cut projection | ✓ |

성격: Raw 위 카타모피즘의 image 우주 (Bool, Nat, Cut).
**Nat213Bridge** 가 Lib.Math.NatHelpers 의 PureNat 사용 (add_mul
등 Lean Nat helpers).

### 1.6 `Theory/Tower/` — pair-based number towers (3 files)

| File | Lines | Role | Spec |
|---|---|---|---|
| NatPairToInt.lean   | ?  | ℕ × ℕ → ℤ (subNatNat) | ✓ |
| NatPairToQPos.lean  | ?  | Nat213 × Nat213 → ℚ_+ | ✓ |
| NatTripleToZ2.lean  | ?  | ℕ³ → ℤ² | ✓ |

성격: Grothendieck completion pattern.  모두 spec 정합 —
Internal.Int213 + Meta.Tactic.Nat213 만.

### 1.7 `Theory/CDDouble/` — Cayley-Dickson doubling (3 files)

| File | Lines | Role | Spec |
|---|---|---|---|
| UniversalOrder4.lean         | ?  | order-4 universal claim | ✓ |
| GenericLiftDemo.lean         | ?  | lift demo | ✓ |
| **UniversalInduction.lean**  | 47 | CD doubling induction | ✗ → 5× Lib.Math.CayleyDickson |

성격: Cayley-Dickson tower 의 universal pattern.
UniversalInduction 은 Lib 의 5개 CayleyDickson level (L4T, L5T, L6T,
Cayley, Lipschitz) 사용 — Lib 콘텐츠.

### 1.8 `Theory/Tools/` — certificate tools (1 file)

| File | Lines | Role | Spec |
|---|---|---|---|
| **CertChecker.lean** | 153 | precision certificate verifier | ✗ → 2× Lib.Physics |

성격: 명백히 Lib.Physics 의 결과 (AlphaEM brackets, Basel bound)
를 verify.  Theory 가 Lib 결과를 cite — 역방향.  Lib 로 이동
명백.

### 1.9 Top-level aggregators (3 files)

- `Theory/API.lean`: TH-A + TH-B re-export shim. ✓
- `Theory/Atomicity.lean`: Atomicity cluster aggregator. ✓
- `Theory/Raw.lean`: Raw cluster aggregator. ✓

## 2. Ring violations — 8 files

```
┌──────────────────────────────────────────────────────────────────────┐
│ # │ File                                  │ Lines │ Lib import       │
├──────────────────────────────────────────────────────────────────────┤
│ 1 │ Atomicity/ArityForcingGeneral.lean    │  98   │ Math.Pigeonhole  │
│ 2 │ CDDouble/UniversalInduction.lean      │  47   │ 5× CayleyDickson │
│ 3 │ Closed/Nat213Bridge.lean              │ 415   │ NatHelpers.PureNat │
│ 4 │ Nat213/AlgebraicGeometry.lean         │ 186   │ Topology, CayleyDickson │
│ 5 │ Nat213/AtomicityCorrespondence.lean   │  56   │ Simplex, UniverseChain │
│ 6 │ Nat213/RotationGeometry.lean          │ 259   │ Topology.EulerChi │
│ 7 │ Raw/Mobius.lean                       │  78   │ Math.Tactic.Ring213 │
│ 8 │ Tools/CertChecker.lean                │ 153   │ 2× Physics       │
└──────────────────────────────────────────────────────────────────────┘
```

### 2.1 Processing options per violation

| # | File | Recommended action |
|---|---|---|
| 1 | ArityForcingGeneral | **Inline pigeonhole core** (or move to Lib/Math/Pigeonhole nearby).  The general-arity ruling-out is conceptually Theory; the pigeonhole lemma is a small combinatorial fact.  Option (a): replicate the needed Pigeonhole core in `Meta/Tactic/` or inside the file.  Option (b): move the file to `Lib/Math/Atomicity/`. |
| 2 | CDDouble/UniversalInduction | **Move to `Lib/Math/CayleyDickson/UniversalInduction.lean`**.  Uses 5 CD lemmas at L4T/L5T/L6T levels — Lib content. |
| 3 | Closed/Nat213Bridge (415 lines, biggest) | **Inline the PureNat helpers used** (likely `add_mul` etc.) into the file or `Meta/Tactic/Nat213`.  Bridge belongs in Theory (it's a Layer 1 ↔ Layer 2 isomorphism proof). |
| 4 | Nat213/AlgebraicGeometry | **Move to `Lib/Math/AlgebraicGeometry/Nat213.lean`** — uses Topology + CayleyDickson, Lib content. |
| 5 | Nat213/AtomicityCorrespondence | Marginal.  Uses Simplex.Counts (combinatorial) + UniverseChain.PairAxes (algebra).  Option (a): inline the small `2 = NT, 3 = NS, 3+2 = d` constants.  Option (b): move to Lib. |
| 6 | Nat213/RotationGeometry | **Move to `Lib/Math/Geometry/Nat213Rotation.lean`** — 259-line geometric application, Lib content. |
| 7 | Raw/Mobius | **Split**: keep core Mobius statements in Theory (the bridge theorem is interesting Theory result), move Ring213-using proofs to `Lib/Math/Mobius/` (the polynomial manipulations).  Or inline Ring213's needed parts. |
| 8 | Tools/CertChecker | **Move to `Lib/Physics/Certificates/Checker.lean`** — verifies Lib.Physics results, definitively Lib content. |

### 2.2 Priority

1. **Tools/CertChecker → Lib/Physics/Certificates/** (easy, no ambiguity, Theory→Lib reversal cleanest).
2. **CDDouble/UniversalInduction → Lib/Math/CayleyDickson/** (easy, clearly Lib).
3. **Nat213/{AlgebraicGeometry, RotationGeometry} → Lib/Math/Geometry/** (445 lines combined, clearly Lib).
4. **Atomicity/ArityForcingGeneral**: small inline of pigeonhole fragment.
5. **Closed/Nat213Bridge (415 lines)**: largest file with smallest Lib dep (1 helper). Inline likely.
6. **Nat213/AtomicityCorrespondence**: inline constants.
7. **Raw/Mobius**: split (most subtle — Mobius bridge is Theory but the polynomial-ring proof is Lib).

After all 7, **0 Theory→Lib imports** in `Theory/`.

## 3. Character verdict

The Theory ring's **35-37 files of 48** are clean spec-compliant Raw
axiom material.  The remaining 8 are migration candidates per the
above options.

The cluster taxonomy is sound:
- `Raw/` = axiom public surface
- `Atomicity/` = forced-shape proofs (pure-ℕ, no Raw)
- `Internal/` = implementation detail
- `Closed/` = catamorphism fixed-point image universes
- `Nat213/` = inductive Layer 2 (mirror of Closed/Nat213)
- `Tower/` = Grothendieck pattern (pair → completion)
- `CDDouble/` = Cayley-Dickson universal pattern
- `Tools/` = certificate utilities (← but its lone file is Lib-bound)

Once the 8 violations are processed, Theory ring is in a clean
canonical state per ARCHITECTURE.md (2026-05-12).
