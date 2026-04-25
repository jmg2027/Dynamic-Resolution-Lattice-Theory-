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

/-- **Tree-level slash helper**: cmp 으로 canonicalize 한 Tree slash.
    RawBy.slash 의 underlying val 을 추출 한 helper. -/
def slashTree (cmp : Tree → Tree → Ordering) (x y : Tree) : Tree :=
  match cmp x y with
  | .lt => .slash x y
  | .gt => .slash y x
  | .eq => .slash x y

/-- slashTree 가 commutative (CmpProps 만 사용). -/
theorem slashTree_comm (cmp : Tree → Tree → Ordering) (h : CmpProps cmp)
    (x y : Tree) (hxy : x ≠ y) :
    slashTree cmp x y = slashTree cmp y x := by
  have hsw := h.swap x y
  unfold slashTree
  cases hxy_cmp : cmp x y with
  | lt =>
      have hyx_cmp : cmp y x = .gt := by
        rw [hxy_cmp] at hsw
        cases hyx_val : cmp y x with
        | lt => rw [hyx_val] at hsw; cases hsw
        | eq => rw [hyx_val] at hsw; cases hsw
        | gt => rfl
      rw [hyx_cmp]
  | eq =>
      have hxy_val : x = y := (h.eq_iff x y).mp hxy_cmp
      exact absurd hxy_val hxy
  | gt =>
      have hyx_cmp : cmp y x = .lt := by
        rw [hxy_cmp] at hsw
        cases hyx_val : cmp y x with
        | lt => rfl
        | eq => rw [hyx_val] at hsw; cases hsw
        | gt => rw [hyx_val] at hsw; cases hsw
      rw [hyx_cmp]

/-- RawBy.slash 의 val = slashTree.  Tree-level 등치 — 모든 cases. -/
theorem RawBy_slash_val (cmp : Tree → Tree → Ordering) (h : CmpProps cmp)
    (x y : RawBy cmp) (hxy : x ≠ y) :
    (RawBy.slash cmp h x y hxy).val = slashTree cmp x.val y.val := by
  unfold RawBy.slash slashTree
  split
  · rename_i hc
    show x.val.slash y.val = (match cmp x.val y.val with
      | .lt => x.val.slash y.val
      | .gt => y.val.slash x.val
      | .eq => x.val.slash y.val)
    rw [hc]
  · rename_i hc
    show y.val.slash x.val = (match cmp x.val y.val with
      | .lt => x.val.slash y.val
      | .gt => y.val.slash x.val
      | .eq => x.val.slash y.val)
    rw [hc]
  · rename_i hc
    have hxy_val : x.val = y.val := (h.eq_iff x.val y.val).mp hc
    exact absurd (Subtype.ext hxy_val) hxy

/-- **Polymorphic RawBy.slash_comm**: Subtype.ext 로 val 비교 →
    slashTree_comm 적용. -/
theorem RawBy.slash_comm (cmp : Tree → Tree → Ordering) (h : CmpProps cmp)
    (x y : RawBy cmp) (hxy : x ≠ y) :
    RawBy.slash cmp h x y hxy = RawBy.slash cmp h y x (Ne.symm hxy) := by
  apply Subtype.ext
  rw [RawBy_slash_val, RawBy_slash_val]
  exact slashTree_comm cmp h x.val y.val
    (fun heq => hxy (Subtype.ext heq))

end E213.Research.CmpIndependence

namespace E213.Research.CmpIndependence

open E213.Firmware E213.Firmware.Internal

/-- canonicalBy slash 의 lt 추출. -/
theorem canonicalBy_slash_lt {cmp : Tree → Tree → Ordering}
    {x y : Tree} (h : canonicalBy cmp (.slash x y) = true) :
    cmp x y = .lt := by
  unfold canonicalBy at h
  rw [Bool.and_eq_true] at h
  obtain ⟨_, hlt_raw⟩ := h
  match hm : cmp x y with
  | .lt => rfl
  | .eq => rw [hm] at hlt_raw; cases hlt_raw
  | .gt => rw [hm] at hlt_raw; cases hlt_raw

end E213.Research.CmpIndependence

namespace E213.Research.CmpIndependence

open E213.Firmware E213.Firmware.Internal

/-- **RawBy.recAux**: structural recursion on Tree, canonical
    form re-assembled via cmp-parameterized RawBy.slash. -/
private noncomputable def RawBy.recAux {cmp : Tree → Tree → Ordering}
    (hP : CmpProps cmp)
    {motive : RawBy cmp → Sort u}
    (a_case : motive (RawBy.a cmp))
    (b_case : motive (RawBy.b cmp))
    (slash_case : ∀ (x y : RawBy cmp) (hxy : x ≠ y),
                  motive x → motive y →
                  motive (RawBy.slash cmp hP x y hxy)) :
    ∀ (t : Tree) (hcanon : canonicalBy cmp t = true),
        motive ⟨t, hcanon⟩ := by
  intro t
  induction t with
  | a => intro _; exact a_case
  | b => intro _; exact b_case
  | slash x y ihx ihy =>
      intro hcanon
      have hc := hcanon
      unfold canonicalBy at hc
      rw [Bool.and_eq_true, Bool.and_eq_true] at hc
      obtain ⟨⟨hx, hy⟩, _⟩ := hc
      have hcmp := canonicalBy_slash_lt hcanon
      let x' : RawBy cmp := ⟨x, hx⟩
      let y' : RawBy cmp := ⟨y, hy⟩
      have hne : x' ≠ y' := by
        intro heq
        have hxy : x = y := congrArg Subtype.val heq
        rw [hxy] at hcmp
        rw [(hP.eq_iff y y).mpr rfl] at hcmp
        cases hcmp
      have heq : (⟨.slash x y, hcanon⟩ : RawBy cmp) =
                  RawBy.slash cmp hP x' y' hne := by
        apply Subtype.ext
        rw [RawBy_slash_val]
        unfold slashTree
        rw [hcmp]
      rw [heq]
      exact slash_case x' y' hne (ihx hx) (ihy hy)

/-- **Custom RawBy eliminator** (cmp-parameterized). -/
@[elab_as_elim]
noncomputable def RawBy.rec {cmp : Tree → Tree → Ordering}
    (hP : CmpProps cmp)
    {motive : RawBy cmp → Sort u}
    (a_case : motive (RawBy.a cmp))
    (b_case : motive (RawBy.b cmp))
    (slash_case : ∀ (x y : RawBy cmp) (hxy : x ≠ y),
                  motive x → motive y →
                  motive (RawBy.slash cmp hP x y hxy))
    (r : RawBy cmp) : motive r :=
  RawBy.recAux hP a_case b_case slash_case r.val r.property

end E213.Research.CmpIndependence

namespace E213.Research.CmpIndependence

open E213.Firmware E213.Firmware.Internal

/-- DecidableEq on RawBy. -/
instance (cmp : Tree → Tree → Ordering) : DecidableEq (RawBy cmp) :=
  fun x y => by
    rcases decEq x.val y.val with hne | heq
    · exact .isFalse (fun h => hne (congrArg Subtype.val h))
    · exact .isTrue (Subtype.ext heq)

/-- **Transport**: RawBy cmp1 → RawBy cmp2 via RawBy.rec.
    Mingu hint: "변환 자체 가 Lens" — base+slash 를 cmp2 의
    constructor 로 하는 fold. -/
noncomputable def transport (cmp1 cmp2 : Tree → Tree → Ordering)
    (h1 : CmpProps cmp1) (h2 : CmpProps cmp2)
    (r : RawBy cmp1) : RawBy cmp2 :=
  RawBy.rec h1 (motive := fun _ => RawBy cmp2)
    (RawBy.a cmp2)
    (RawBy.b cmp2)
    (fun _ _ _ ih_x ih_y =>
      if hne : ih_x ≠ ih_y then RawBy.slash cmp2 h2 ih_x ih_y hne
      else RawBy.a cmp2)
    r

end E213.Research.CmpIndependence

namespace E213.Research.CmpIndependence

open E213.Firmware E213.Firmware.Internal

/-- transport of RawBy.a. -/
theorem transport_a (cmp1 cmp2 : Tree → Tree → Ordering)
    (h1 : CmpProps cmp1) (h2 : CmpProps cmp2) :
    transport cmp1 cmp2 h1 h2 (RawBy.a cmp1) = RawBy.a cmp2 := rfl

/-- transport of RawBy.b. -/
theorem transport_b (cmp1 cmp2 : Tree → Tree → Ordering)
    (h1 : CmpProps cmp1) (h2 : CmpProps cmp2) :
    transport cmp1 cmp2 h1 h2 (RawBy.b cmp1) = RawBy.b cmp2 := rfl

end E213.Research.CmpIndependence

namespace E213.Research.CmpIndependence

open E213.Firmware E213.Firmware.Internal

-- transport_slash (recursion equation) 은 noncomputable rec 의
-- definitional reduction 가 명시 적 generation 안 됨 → rfl 안
-- 통과.  Manual reduction 또는 다른 induction 도구 필요 (Phase
-- 3.5).  현재 transport_a, transport_b 의 reduction 만 establish.

end E213.Research.CmpIndependence
