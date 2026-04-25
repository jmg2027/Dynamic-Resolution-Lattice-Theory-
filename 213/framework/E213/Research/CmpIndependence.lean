import E213.Firmware.Raw

/-!
# Research.CmpIndependence: cmp 선택 의 axiom-무관 성 (foundational)

`IMPLEMENTATION.md §5` 의 cmp-independence meta-theorem 의
foundational layer 형식 화.

## Internal access 정당성

이 파일 은 `E213.Firmware.Internal` 을 `open` 함.  CLAUDE.md
일반 규칙 ("user code 에서 Internal open 금지") 의 **명시 적
예외** — 이 파일 자체 가 encoding scaffolding (Tree, Tree.cmp)
의 axiom 무관 성 검증.

## 형식화 단계

Phase 1 (이 파일):
- `CmpProps`: cmp 의 well-behaved order 조건 추상화.
- `Tree.cmp` 가 CmpProps 만족.
- `cmpRev` 도 CmpProps 만족 (involutive).
- `canonicalBy cmp`, `RawBy cmp`: cmp-parametric.
- 원래 Raw 와의 일치: `canonicalBy Tree.cmp = Tree.canonical`.

Phase 2 (future): bijection RawBy cmp1 ≃ RawBy cmp2.
-/

namespace E213.Research.CmpIndependence

open E213.Firmware E213.Firmware.Internal

/-- **CmpProps**: cmp 의 well-behaved order 조건. -/
structure CmpProps (cmp : Tree → Tree → Ordering) : Prop where
  eq_iff : ∀ x y, cmp x y = .eq ↔ x = y
  swap : ∀ x y, cmp x y = (cmp y x).swap

/-- Tree.cmp 가 CmpProps 만족. -/
theorem Tree_cmp_props : CmpProps Tree.cmp where
  eq_iff := Tree.cmp_eq_iff
  swap := Tree.cmp_swap

/-- cmp 의 reverse: cmpRev x y := (cmp x y).swap. -/
def cmpRev (cmp : Tree → Tree → Ordering) (x y : Tree) : Ordering :=
  (cmp x y).swap

theorem Ordering_swap_swap (o : Ordering) : o.swap.swap = o := by
  cases o <;> rfl

/-- cmpRev 도 CmpProps 만족 (involutive). -/
theorem cmpRev_props (cmp : Tree → Tree → Ordering) (h : CmpProps cmp) :
    CmpProps (cmpRev cmp) where
  eq_iff := by
    intro x y
    unfold cmpRev
    constructor
    · intro hsw
      have : cmp x y = .eq := by
        cases hcmp : cmp x y with
        | eq => rfl
        | lt => rw [hcmp] at hsw; cases hsw
        | gt => rw [hcmp] at hsw; cases hsw
      exact (h.eq_iff x y).mp this
    · intro hxy
      rw [hxy]
      have : cmp y y = .eq := (h.eq_iff y y).mpr rfl
      rw [this]; rfl
  swap := by
    intro x y
    unfold cmpRev
    rw [h.swap x y, Ordering_swap_swap]

end E213.Research.CmpIndependence

namespace E213.Research.CmpIndependence

open E213.Firmware E213.Firmware.Internal

/-- **canonicalBy cmp**: Tree 가 cmp-canonical (slash 의 left
    child 가 cmp 로 strictly less). -/
def canonicalBy (cmp : Tree → Tree → Ordering) : Tree → Bool
  | .a => true
  | .b => true
  | .slash x y =>
      canonicalBy cmp x && canonicalBy cmp y &&
      (match cmp x y with | .lt => true | _ => false)

/-- **RawBy cmp**: cmp-canonical Tree 의 subtype. -/
def RawBy (cmp : Tree → Tree → Ordering) : Type :=
  { t : Tree // canonicalBy cmp t = true }

/-- Original Tree.cmp 사용 시 canonicalBy = Tree.canonical. -/
theorem canonicalBy_Tree_cmp (t : Tree) :
    canonicalBy Tree.cmp t = t.canonical := by
  induction t with
  | a => rfl
  | b => rfl
  | slash x y ihx ihy =>
      unfold canonicalBy Tree.canonical
      rw [ihx, ihy]
      rfl

/-- 따라서 RawBy Tree.cmp 의 underlying predicate = Tree.canonical. -/
theorem RawBy_Tree_cmp_iff (t : Tree) :
    canonicalBy Tree.cmp t = true ↔ t.canonical = true := by
  rw [canonicalBy_Tree_cmp]

/-- **Polymorphic constructors**: RawBy cmp 의 base 와 slash. -/
def RawBy.a (cmp : Tree → Tree → Ordering) : RawBy cmp := ⟨.a, rfl⟩
def RawBy.b (cmp : Tree → Tree → Ordering) : RawBy cmp := ⟨.b, rfl⟩

end E213.Research.CmpIndependence

namespace E213.Research.CmpIndependence

open E213.Firmware E213.Firmware.Internal

/-- **Polymorphic slash**: RawBy cmp 의 slash 가 cmp 으로
    canonicalize.  Original Raw.slash 의 generalization. -/
def RawBy.slash (cmp : Tree → Tree → Ordering) (h : CmpProps cmp)
    (x y : RawBy cmp) (hxy : x ≠ y) : RawBy cmp :=
  match hc : cmp x.val y.val with
  | .lt => ⟨.slash x.val y.val, by
      unfold canonicalBy
      rw [x.property, y.property, hc]
      rfl⟩
  | .gt =>
      have hyx : cmp y.val x.val = .lt := by
        have := h.swap x.val y.val
        rw [hc] at this
        cases hyx_val : cmp y.val x.val with
        | lt => rfl
        | eq => rw [hyx_val] at this; cases this
        | gt => rw [hyx_val] at this; cases this
      ⟨.slash y.val x.val, by
        unfold canonicalBy
        rw [x.property, y.property, hyx]
        rfl⟩
  | .eq =>
      have hxy_val : x.val = y.val := (h.eq_iff x.val y.val).mp hc
      absurd (Subtype.ext hxy_val) hxy

-- Polymorphic slash_comm 은 dependent match 의 추가 도구 필요
-- (Phase 2.5).  RawBy.slash 자체 가 polymorphic 으로 정의 됨이 Phase 2 의 결과.

end E213.Research.CmpIndependence
