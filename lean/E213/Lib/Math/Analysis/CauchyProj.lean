import E213.Lib.Math.Analysis.CauchyComplete

/-!
# Analysis.CauchyProj — vertical-internal projection on CauchyCutSeq

The vertical-internal projection meta-pattern (Bool213 / RawCut)
extends naturally to a third domain (Cauchy sequence + modulus).

## Domain catalog (post-Option-C 3-domain table)

| domain | object | projection | base canonical form |
|---|---|---|---|
| Bool213 | Raw | booleanProj | T or F |
| RawCut | Raw → Raw → Raw | cutBooleanProj | Bool-valued cut |
| **CauchyCutSeq** | **structure** | **cauchyProj** | **constant sequence at limit** |


## Definition

`cauchyProj ccs := constCauchyCutSeq ccs.limit` — normalizes a Cauchy seq
into "constant at limit" form.

## Properties (parallel across domains)

  - **closure**: `cauchyProj ccs` is always a constCauchyCutSeq image.
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
    Compatibility of vertical-external (limit) and vertical-internal (cauchyProj).  rfl. -/
theorem cauchyProj_limit (ccs : CauchyCutSeq) :
    (cauchyProj ccs).limit = ccs.limit := rfl

/-- **Idempotence**: `cauchyProj² = cauchyProj`.  Full equality on the
    CauchyCutSeq structure, rfl (constCauchyCutSeq ∘ limit ∘ constCauchyCutSeq ∘ limit
    = constCauchyCutSeq ∘ limit). -/
theorem cauchyProj_idempotent (ccs : CauchyCutSeq) :
    cauchyProj (cauchyProj ccs) = cauchyProj ccs := rfl

/-- **Image predicate**: ccs is a cauchyProj image — i.e. constCauchyCutSeq
    form.  "ccs.cs i = ccs.limit for all i" (informally). -/
def IsConstAtLimit (ccs : CauchyCutSeq) : Prop :=
  ccs = cauchyProj ccs

/-- If constant-at-limit, then a fixed point of cauchyProj.  trivially. -/
theorem cauchyProj_id_of_isConst (ccs : CauchyCutSeq)
    (h : IsConstAtLimit ccs) : cauchyProj ccs = ccs := h.symm

/-- Converse: if a cauchyProj fixed point, then constant-at-limit. -/
theorem isConst_of_cauchyProj_id (ccs : CauchyCutSeq)
    (h : cauchyProj ccs = ccs) : IsConstAtLimit ccs :=
  h.symm

/-- **Fixed-point ↔ image** (parallel to Bool213 / RawCut — post-Option-C
    Nat213 is a Nat-side projection, so this pattern does not apply there). -/
theorem cauchyProj_id_iff_isConst (ccs : CauchyCutSeq) :
    cauchyProj ccs = ccs ↔ IsConstAtLimit ccs :=
  ⟨isConst_of_cauchyProj_id ccs, fun h => (cauchyProj_id_of_isConst ccs h)⟩

/-- Worked demonstration: the cauchyProj of a constCauchyCutSeq is itself. -/
example (c : Nat → Nat → Bool) :
    cauchyProj (constCauchyCutSeq c) = constCauchyCutSeq c := rfl

end E213.Lib.Math.Analysis.CauchyProj
