import E213.Research.SemanticAtom

/-!
# Research.SubtypeInstance: distinguishing-closed predicate 의 sub-instance

User directive (2026-04-25): Subtype 의 distinguishing-closed
가정 의 framework 안 내부화.

`{r : Raw // P r}` 의 HasDistinguishing instance.

## Design note

기본 기 정 combine (Raw.slash) 의 commutativity 의 형식 이
nested Subtype (Raw 가 자신 도 Subtype) 의 elaborator unfold 의
한계 봉착.  대신 *degenerate combine* 으로 instance 형식.

→ Sub-instance 의 *존재* 형식 됨 — meaningful combine 의 design
은 Lean infrastructure 의 제약 으로 추가 작업 필요.
-/

namespace E213.Research.SubtypeInstance

open E213.Firmware E213.Hypervisor
open E213.Research.SemanticAtom

/-- distinguishing-closed predicate 위 의 sub-instance (degenerate
    combine).  combine 의 결과 가 항상 a (first base) — degenerate
    하지만 valid HasDistinguishing instance. -/
def subtypeHasDistinguishing (P : Raw → Prop)
    (h_a : P Raw.a) (h_b : P Raw.b) :
    HasDistinguishing {r : Raw // P r} where
  a := ⟨Raw.a, h_a⟩
  b := ⟨Raw.b, h_b⟩
  distinct := by
    intro heq
    have hval : (Raw.a : Raw) = Raw.b :=
      congrArg Subtype.val heq
    exact absurd hval (by decide)
  combine := fun _ _ => ⟨Raw.a, h_a⟩
  combine_sym := fun _ _ => rfl

end E213.Research.SubtypeInstance

namespace E213.Research.SubtypeInstance

open E213.Firmware E213.Hypervisor
open E213.Research.SemanticAtom

/-- Universal morphism Raw → {r : Raw // P r} via degenerate
    sub-instance.  대부분 Raw 가 a 에 collapse — degenerate
    instance 의 자연 결과. -/
def subtypeUniversalMorphism (P : Raw → Prop)
    (h_a : P Raw.a) (h_b : P Raw.b) : Raw → {r : Raw // P r} :=
  @universalMorphism {r : Raw // P r} (subtypeHasDistinguishing P h_a h_b)

end E213.Research.SubtypeInstance
