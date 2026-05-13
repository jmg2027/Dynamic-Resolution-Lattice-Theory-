import E213.Theory.Closed.Bool213
import E213.Theory.Closed.Nat213

/-!
# Theory.Closed.RawCut — Lean-free cut prototype

기존 `Lib/Math/Real213/CutPoset.lean` 의 cut 표현은
`Nat → Nat → Bool` — Lean 의 Nat 와 Bool 사용.

이 모듈은 **완전 Lean-free** 시범:
  - 입력: 두 Raw (numerator m, denominator k as Method A Nat213 chain)
  - 출력: Raw (Bool213 의 T 또는 F)

`RawCut := Raw → Raw → Raw` — Raw 만으로 cut 정의.  외부 type 격리
레이어 한 발 더 안쪽.

## 의의 (G84 압축 thesis 의 logical 끝점)

> 213 의 본격 닫힌 우주: substantial content 에 Lean type 사용 안 함.
> Lean type 은 boundary layer (Theory/Raw/Core 의 Subtype/inductive) 만.

이 시범으로 cut 도 Lean-free 가능 입증.  같은 패턴으로 Cauchy seq,
모든 cut 위 정리들을 Lean-free 로 변환 가능.
-/

namespace E213.Theory.Closed.RawCut

open E213.Theory
open E213.Theory.Closed.Bool213 (T F)

/-- Lean-free cut type — 입력 출력 모두 Raw. -/
abbrev RawCut := Raw → Raw → Raw

/-- 모든 입력에서 T 반환하는 trivial cut. -/
def constTrueCut : RawCut := fun _ _ => T

/-- 모든 입력에서 F 반환하는 trivial cut. -/
def constFalseCut : RawCut := fun _ _ => F

/-- Pointwise equality on Raw cuts (Lean-free version of cutEq).
    함수 비교 → 점별 Raw 등호. -/
def rawCutEq (cx cy : RawCut) : Prop := ∀ m k, cx m k = cy m k

/-- Pointwise inequality (Lean-free version of cutLe).
    `cy m k = T → cx m k = T` 형태. -/
def rawCutLe (cx cy : RawCut) : Prop :=
  ∀ m k, cy m k = T → cx m k = T

/-! ### Equivalence + order properties (Lean-free) -/

theorem rawCutEq_refl (c : RawCut) : rawCutEq c c := fun _ _ => rfl

theorem rawCutEq_symm (cx cy : RawCut) (h : rawCutEq cx cy) : rawCutEq cy cx :=
  fun m k => (h m k).symm

theorem rawCutEq_trans (cx cy cz : RawCut)
    (h1 : rawCutEq cx cy) (h2 : rawCutEq cy cz) : rawCutEq cx cz :=
  fun m k => (h1 m k).trans (h2 m k)

theorem rawCutLe_refl (c : RawCut) : rawCutLe c c := fun _ _ h => h

theorem rawCutLe_trans (cx cy cz : RawCut)
    (h1 : rawCutLe cx cy) (h2 : rawCutLe cy cz) : rawCutLe cx cz :=
  fun m k hcz => h1 m k (h2 m k hcz)

/-- rawCutEq → rawCutLe (both directions). -/
theorem rawCutLe_of_rawCutEq (cx cy : RawCut) (h : rawCutEq cx cy) :
    rawCutLe cx cy := fun m k hy => (h m k).symm ▸ hy

/-- 동작 시범. -/
example : rawCutEq constTrueCut constTrueCut := rawCutEq_refl _
example : rawCutLe constTrueCut constTrueCut := rawCutLe_refl _

end E213.Theory.Closed.RawCut

namespace E213.Theory.Closed.RawCut

open E213.Theory
open E213.Theory.Closed.Bool213 (T F booleanProj booleanProj_T booleanProj_F
                                  booleanProj_isBool booleanProj_idempotent
                                  boolValue boolValue_booleanProj)

/-! ### Vertical-internal projection on RawCut

leavesCountRaw (Nat213) / booleanProj (Bool213) 의 함수공간 (RawCut) 버전.
임의 RawCut 의 각 점 출력을 booleanProj 통과 → 출력값이 항상 {T, F}.

함수 등호는 funext 필요 (axiom-cost 발생).  대신 **rawCutEq** (pointwise
Bool eq, Lean-free pattern) 으로 idempotence 표현 — 같은 도메인에서
같은 메타 패턴이 함수공간에서도 작동 입증.

세 도메인 (Nat213, Bool213, RawCut) 위 vertical-internal projection 이
모두 같은 closure + idempotence 형태:
  - Nat213:  leavesCountRaw r = leavesCountRaw² r,    output ∈ chain
  - Bool213: booleanProj r = booleanProj² r,           output ∈ {T, F}
  - RawCut:  cutBooleanProj cx ≈ cutBooleanProj² cx,   output ∈ Bool213-cut
-/

/-- Cut 위 vertical-internal projection — 점별 booleanProj. -/
def cutBooleanProj (cx : RawCut) : RawCut :=
  fun m k => booleanProj (cx m k)

/-- **Closure**: cutBooleanProj 의 점값이 항상 T 또는 F. -/
theorem cutBooleanProj_isBool (cx : RawCut) (m k : Raw) :
    cutBooleanProj cx m k = T ∨ cutBooleanProj cx m k = F :=
  booleanProj_isBool (cx m k)

/-- **Idempotence (pointwise)**: `cutBooleanProj² ≈ cutBooleanProj` via rawCutEq.
    funext 안 쓰고 점별 Bool eq — Real213 cutEq 와 같은 pattern. -/
theorem cutBooleanProj_idempotent (cx : RawCut) :
    rawCutEq (cutBooleanProj (cutBooleanProj cx)) (cutBooleanProj cx) :=
  fun m k => booleanProj_idempotent (cx m k)

/-! ### Fixed-point 특성화 — Bool-valued 인 cut 들이 정확히 fixed point -/

/-- Cut 의 점값이 모두 Bool213 ({T, F}) 안. -/
def IsBoolValued (cx : RawCut) : Prop :=
  ∀ m k, cx m k = T ∨ cx m k = F

/-- Bool-valued 면 cutBooleanProj 의 fixed point (rawCutEq 위). -/
theorem cutBooleanProj_id_of_isBool (cx : RawCut) (h : IsBoolValued cx) :
    rawCutEq (cutBooleanProj cx) cx := by
  intro m k
  show booleanProj (cx m k) = cx m k
  rcases h m k with hT | hF
  · rw [hT]; exact booleanProj_T
  · rw [hF]; exact booleanProj_F

/-- 역방향: cutBooleanProj 의 fixed point 면 Bool-valued. -/
theorem isBool_of_cutBooleanProj_id (cx : RawCut)
    (h : rawCutEq (cutBooleanProj cx) cx) : IsBoolValued cx := by
  intro m k
  have hck : booleanProj (cx m k) = cx m k := h m k
  rcases booleanProj_isBool (cx m k) with hT | hF
  · left; rw [← hck]; exact hT
  · right; rw [← hck]; exact hF

/-- **Fixed-point 특성화**: cutBooleanProj 가 cx 를 그대로 두는 것 ↔ cx 가
    Bool-valued.  vertical-internal projection 의 정확한 image 결정. -/
theorem cutBooleanProj_id_iff_isBool (cx : RawCut) :
    rawCutEq (cutBooleanProj cx) cx ↔ IsBoolValued cx :=
  ⟨isBool_of_cutBooleanProj_id cx, cutBooleanProj_id_of_isBool cx⟩

/-! ### Concrete examples — 두 trivial cut 위 fixed point -/

theorem cutBooleanProj_constTrue :
    rawCutEq (cutBooleanProj constTrueCut) constTrueCut :=
  fun _ _ => booleanProj_T

theorem cutBooleanProj_constFalse :
    rawCutEq (cutBooleanProj constFalseCut) constFalseCut :=
  fun _ _ => booleanProj_F

/-! ### Boundary mapping — RawCut → (Raw → Raw → Bool)

Nat213 의 `value` / Bool213 의 `boolValue` 와 평행: 함수공간의 boundary.
점별 boolValue.

세 도메인 평행 완성:
  Nat213:  value : Raw → Nat                        + value_leavesCountRaw_general
  Bool213: boolValue : Raw → Bool                    + boolValue_booleanProj
  RawCut:  cutBoolValue : RawCut → (Raw → Raw → Bool) + cutBoolValue_cutBooleanProj
-/

/-- Cut 의 boundary projection — 점별 boolValue. -/
def cutBoolValue (cx : RawCut) : Raw → Raw → Bool :=
  fun m k => boolValue (cx m k)

/-- **Boundary commutativity** (pointwise): cutBoolValue ∘ cutBooleanProj = cutBoolValue.
    수직-외부 + 수직-내부 호환의 점별 표현. -/
theorem cutBoolValue_cutBooleanProj (cx : RawCut) (m k : Raw) :
    cutBoolValue (cutBooleanProj cx) m k = cutBoolValue cx m k :=
  boolValue_booleanProj (cx m k)

end E213.Theory.Closed.RawCut
