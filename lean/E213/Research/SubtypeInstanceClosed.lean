import E213.Research.SemanticAtom

/-!
# Research.SubtypeInstanceClosed: distinguishing-closed subtype
의 slash-based combine instance

PAPER1 §8.2 의 third closed boundary 의 fix: nested-Subtype
elaborator 우회 via SlashClosed typeclass + decidable equality
on Raw.

## 핵심

`SlashClosed P`: P 가 distinct slash arguments 위 closed 임을
data 로 carry.  이 가정 하 에 `{r : Raw // P r}` 위 의 slash-based
combine 가 well-defined + commutative.

`SubtypeInstance.lean` 의 degenerate combine 을 대체.
-/

namespace E213.Research.SubtypeInstanceClosed

open E213.Firmware E213.Hypervisor
open E213.Research.SemanticAtom

/-- `P` 가 `Raw.slash` 위 closed: distinct args 위 P 보존. -/
class SlashClosed (P : Raw → Prop) : Prop where
  closed : ∀ {x y : Raw} (h : x ≠ y), P x → P y → P (Raw.slash x y h)

end E213.Research.SubtypeInstanceClosed

namespace E213.Research.SubtypeInstanceClosed

open E213.Firmware E213.Hypervisor
open E213.Research.SemanticAtom

/-- Subtype 위 의 slash-based combine.  Equal val 의 경우
    base_a fallback (slash 가 distinct args 만 받기 때문). -/
def subtypeCombine (P : Raw → Prop) [SlashClosed P]
    (h_a : P Raw.a) :
    {r : Raw // P r} → {r : Raw // P r} → {r : Raw // P r} :=
  fun x y =>
    if h : x.val = y.val then ⟨Raw.a, h_a⟩
    else ⟨Raw.slash x.val y.val h,
          SlashClosed.closed h x.property y.property⟩

theorem subtypeCombine_comm (P : Raw → Prop) [SlashClosed P]
    (h_a : P Raw.a) (x y : {r : Raw // P r}) :
    subtypeCombine P h_a x y = subtypeCombine P h_a y x := by
  unfold subtypeCombine
  by_cases h : x.val = y.val
  · have hsym : y.val = x.val := h.symm
    rw [dif_pos h, dif_pos hsym]
  · have hsym : y.val ≠ x.val := fun e => h e.symm
    rw [dif_neg h, dif_neg hsym]
    apply Subtype.ext
    exact Raw.slash_comm _ _ h

end E213.Research.SubtypeInstanceClosed

namespace E213.Research.SubtypeInstanceClosed

open E213.Firmware E213.Hypervisor
open E213.Research.SemanticAtom

/-- **Slash-based HasDistinguishing instance** on
    `{r : Raw // P r}` for distinguishing-closed `P`.
    `SubtypeInstance.lean` 의 degenerate combine 의
    *meaningful* version.  PAPER1 §8.2 의 third closed
    boundary 가 SlashClosed typeclass 와 함께 해소. -/
def subtypeHasDistinguishingClosed (P : Raw → Prop) [SlashClosed P]
    (h_a : P Raw.a) (h_b : P Raw.b) :
    HasDistinguishing {r : Raw // P r} where
  a := ⟨Raw.a, h_a⟩
  b := ⟨Raw.b, h_b⟩
  distinct := by
    intro heq
    have hval : (Raw.a : Raw) = Raw.b := congrArg Subtype.val heq
    exact absurd hval (by decide)
  combine := subtypeCombine P h_a
  combine_sym := subtypeCombine_comm P h_a

end E213.Research.SubtypeInstanceClosed

namespace E213.Research.SubtypeInstanceClosed

open E213.Firmware E213.Hypervisor
open E213.Research.SemanticAtom

/-! ### Concrete instance: `True`-predicate (the trivial slash-closed)

`P := fun _ => True` 가 자명 하 게 SlashClosed.  결과 subtype
`{r : Raw // True}` 는 Raw 와 isomorphic, 그 위 의 instance 가
slash-based combine. -/

instance trueSlashClosed : SlashClosed (fun _ => True) where
  closed := fun _ _ _ => trivial

/-- `{r : Raw // True}` 위 의 slash-based instance.  `Raw` 자체
    의 instance 와 essentially 동치 — meaningful combine. -/
def trueSubtypeInstance : HasDistinguishing {r : Raw // True} :=
  subtypeHasDistinguishingClosed (fun _ => True) trivial trivial

end E213.Research.SubtypeInstanceClosed
