import E213.Lib.Math.Analysis.CauchyComplete

/-!
# Analysis.CauchyProj — vertical-internal projection on CauchyCutSeq

Theory/Closed/* 의 vertical-internal projection 메타 패턴이 4번째 도메인
(Cauchy sequence + modulus) 에서도 작동.

## 도메인 catalog (4 사례)

| domain | object | projection | base canonical form |
|---|---|---|---|
| Bool213 | Raw | booleanProj | T or F |
| RawCut | Raw → Raw → Raw | cutBooleanProj | Bool-valued cut |
| **CauchyCutSeq** | **structure** | **cauchyProj** | **constant sequence at limit** |

(Post-Option-C 2026-05-18: the former Nat213 row with
`leavesCountRaw` has been removed — ℕ₊ now projects to `Nat`
codomain rather than carrying a Raw-internal projection.  See
`seed/CLOSED_FORM_SPEC.md` for the current 3-domain table.)

## 정의

`cauchyProj ccs := constCauchyCutSeq ccs.limit` — Cauchy seq 를
"limit 에서 constant" 형태로 normalize.

## 성질 (다른 도메인과 평행)

  - **closure**: `cauchyProj ccs` 가 항상 constCauchyCutSeq image.
  - **idempotence**: `cauchyProj² = cauchyProj` (functional eq, rfl).
  - **boundary commutativity**: `(cauchyProj ccs).limit = ccs.limit`.
-/

namespace E213.Lib.Math.Analysis.CauchyProj

open E213.Lib.Math.Analysis.CauchyComplete

/-- Vertical-internal projection on CauchyCutSeq.  "Constant sequence
    at limit" canonical form. -/
def cauchyProj (ccs : CauchyCutSeq) : CauchyCutSeq :=
  constCauchyCutSeq ccs.limit

/-- **Boundary commutativity**: `(cauchyProj ccs).limit = ccs.limit`.
    수직-외부 (limit) 와 수직-내부 (cauchyProj) 의 호환.  rfl. -/
theorem cauchyProj_limit (ccs : CauchyCutSeq) :
    (cauchyProj ccs).limit = ccs.limit := rfl

/-- **Idempotence**: `cauchyProj² = cauchyProj`.  CauchyCutSeq 구조 위
    full equality, rfl (constCauchyCutSeq ∘ limit ∘ constCauchyCutSeq ∘ limit
    = constCauchyCutSeq ∘ limit). -/
theorem cauchyProj_idempotent (ccs : CauchyCutSeq) :
    cauchyProj (cauchyProj ccs) = cauchyProj ccs := rfl

/-- **Image predicate**: ccs 가 cauchyProj image — 즉 constCauchyCutSeq
    형태.  "ccs.cs i = ccs.limit for all i" (informally). -/
def IsConstAtLimit (ccs : CauchyCutSeq) : Prop :=
  ccs = cauchyProj ccs

/-- Constant-at-limit 면 cauchyProj 의 fixed point.  trivially. -/
theorem cauchyProj_id_of_isConst (ccs : CauchyCutSeq)
    (h : IsConstAtLimit ccs) : cauchyProj ccs = ccs := h.symm

/-- 역방향: cauchyProj fixed point 면 constant-at-limit. -/
theorem isConst_of_cauchyProj_id (ccs : CauchyCutSeq)
    (h : cauchyProj ccs = ccs) : IsConstAtLimit ccs :=
  h.symm

/-- **Fixed-point ↔ image** (Bool213 / RawCut 와 평행 — post-Option-C
    Nat213 는 Nat 측 projection 이라 이 패턴 적용 안 함). -/
theorem cauchyProj_id_iff_isConst (ccs : CauchyCutSeq) :
    cauchyProj ccs = ccs ↔ IsConstAtLimit ccs :=
  ⟨isConst_of_cauchyProj_id ccs, fun h => (cauchyProj_id_of_isConst ccs h)⟩

/-- 작동 시범: constCauchyCutSeq 의 cauchyProj 는 자기 자신. -/
example (c : Nat → Nat → Bool) :
    cauchyProj (constCauchyCutSeq c) = constCauchyCutSeq c := rfl

end E213.Lib.Math.Analysis.CauchyProj
