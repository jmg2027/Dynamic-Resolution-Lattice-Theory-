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

-- transport_slash 의 manual reduction 은 noncomputable rec 의
-- internal Eq.mpr / cast / Subtype.ext 의 orchestration 필요.
-- Subtype.ext 강등 + recAux Tree-level reduction + Eq.mpr 정리.
-- Phase 3.5 의 진행 — concrete attempt 는 별도.

end E213.Research.CmpIndependence

namespace E213.Research.CmpIndependence

open E213.Firmware E213.Firmware.Internal

-- recAux_slash 보조 정리 (Phase 3.5): RawBy.recAux 가 Tree.slash
-- 입력 시 어떤 형태로 reduce 되는지 명시 — Mingu hint #2.
-- 도전: noncomputable rec 의 reduction 이 자동 부재 라서, manual
-- Eq.mpr / cast 정리 필요.  실제 obstacle (예상):
-- A. Tree.rec.{u} universe.
-- B. (RawBy.slash _).val 의 match 분기.
-- C. (RawBy.slash _).property 의 proof.
-- D. rw [heq] 의 Eq.mpr.
-- E. let-zeta 부재.
-- 이 부분 의 manual orchestration 이 transport_slash 의 마지막
-- 닫음.  추가 simp [Eq.mpr, cast] 가 도움 될 가능성.

end E213.Research.CmpIndependence

namespace E213.Research.CmpIndependence

open E213.Firmware E213.Firmware.Internal

-- Phase 3.5 alternative path: 직접 Tree-level transportTree 정의.
-- noncomputable RawBy.rec 의 reduction 회피.

/-- **Tree-level transport**: canonicalize Tree under cmp2.
    Computable, inductively defined on Tree. -/
def transportTree (cmp2 : Tree → Tree → Ordering) : Tree → Tree
  | .a => .a
  | .b => .b
  | .slash x y => slashTree cmp2 (transportTree cmp2 x) (transportTree cmp2 y)

end E213.Research.CmpIndependence

namespace E213.Research.CmpIndependence

open E213.Firmware E213.Firmware.Internal

/-- transportTree reductions (computable, automatic). -/
theorem transportTree_a (cmp2 : Tree → Tree → Ordering) :
    transportTree cmp2 .a = .a := rfl

theorem transportTree_b (cmp2 : Tree → Tree → Ordering) :
    transportTree cmp2 .b = .b := rfl

theorem transportTree_slash (cmp2 : Tree → Tree → Ordering) (x y : Tree) :
    transportTree cmp2 (.slash x y)
      = slashTree cmp2 (transportTree cmp2 x) (transportTree cmp2 y) := rfl

end E213.Research.CmpIndependence

namespace E213.Research.CmpIndependence

open E213.Firmware E213.Firmware.Internal

/-- slashTree commutativity 의 핵심 산물: canonical input 의 result. -/
theorem slashTree_canonical_input {cmp : Tree → Tree → Ordering}
    (h : CmpProps cmp) (s u : Tree) (hsu : cmp s u = .lt) :
    slashTree cmp s u = .slash s u := by
  unfold slashTree; rw [hsu]

/-- slashTree of {a, b} = canonical .slash result. -/
theorem slashTree_of_pair_eq {cmp : Tree → Tree → Ordering}
    (h : CmpProps cmp) (s u p q : Tree) (hsu : cmp s u = .lt)
    (hpair : (p = s ∧ q = u) ∨ (p = u ∧ q = s)) :
    slashTree cmp p q = .slash s u := by
  rcases hpair with ⟨hp, hq⟩ | ⟨hp, hq⟩
  · rw [hp, hq]; exact slashTree_canonical_input h s u hsu
  · rw [hp, hq]
    have hus : cmp u s = .gt := by
      have hsw := h.swap s u
      rw [hsu] at hsw
      cases hus_val : cmp u s with
      | lt => rw [hus_val] at hsw; cases hsw
      | eq => rw [hus_val] at hsw; cases hsw
      | gt => rfl
    unfold slashTree
    rw [hus]

end E213.Research.CmpIndependence

namespace E213.Research.CmpIndependence

open E213.Firmware E213.Firmware.Internal

/-- **Round-trip on canonical**: f(g(t)) = t for canonical-by-cmp2 t.
    f := transportTree cmp2, g := transportTree cmp1.
    핑계 없는 cases noodge. -/
theorem transportTree_roundtrip
    (cmp1 cmp2 : Tree → Tree → Ordering)
    (h1 : CmpProps cmp1) (h2 : CmpProps cmp2)
    (t : Tree) (hcanon : canonicalBy cmp2 t = true) :
    transportTree cmp2 (transportTree cmp1 t) = t := by
  induction t with
  | a => rfl
  | b => rfl
  | slash s u ihs ihu =>
      have hsu : cmp2 s u = .lt := canonicalBy_slash_lt hcanon
      unfold canonicalBy at hcanon
      rw [Bool.and_eq_true, Bool.and_eq_true] at hcanon
      obtain ⟨⟨hcs, hcu⟩, _⟩ := hcanon
      have ihs' := ihs hcs
      have ihu' := ihu hcu
      rw [transportTree_slash]
      cases hcmp1 : cmp1 (transportTree cmp1 s) (transportTree cmp1 u) with
      | lt =>
          have h_st : slashTree cmp1 (transportTree cmp1 s)
                        (transportTree cmp1 u)
                    = .slash (transportTree cmp1 s) (transportTree cmp1 u) := by
            unfold slashTree; rw [hcmp1]
          rw [h_st, transportTree_slash, ihs', ihu']
          unfold slashTree; rw [hsu]
      | gt =>
          have h_st : slashTree cmp1 (transportTree cmp1 s)
                        (transportTree cmp1 u)
                    = .slash (transportTree cmp1 u) (transportTree cmp1 s) := by
            unfold slashTree; rw [hcmp1]
          rw [h_st, transportTree_slash, ihs', ihu']
          have hus : cmp2 u s = .gt := by
            have hsw := h2.swap s u
            rw [hsu] at hsw
            cases hus_val : cmp2 u s with
            | lt => rw [hus_val] at hsw; cases hsw
            | eq => rw [hus_val] at hsw; cases hsw
            | gt => rfl
          unfold slashTree; rw [hus]
      | eq =>
          have hpq : transportTree cmp1 s = transportTree cmp1 u :=
            (h1.eq_iff _ _).mp hcmp1
          have hsu_eq : s = u := by
            have := ihs'
            rw [hpq] at this
            rw [ihu'] at this
            exact this.symm
          rw [hsu_eq] at hsu
          rw [(h2.eq_iff u u).mpr rfl] at hsu
          cases hsu

end E213.Research.CmpIndependence

namespace E213.Research.CmpIndependence

open E213.Firmware E213.Firmware.Internal

/-- transportTree 가 canonical-by-cmp1 → canonical-by-cmp2.
    g∘f = id 의 symmetric application 으로 injectivity 도출. -/
theorem transportTree_canonical
    (cmp1 cmp2 : Tree → Tree → Ordering)
    (h1 : CmpProps cmp1) (h2 : CmpProps cmp2)
    (t : Tree) (hcanon1 : canonicalBy cmp1 t = true) :
    canonicalBy cmp2 (transportTree cmp2 t) = true := by
  induction t with
  | a => rfl
  | b => rfl
  | slash s u ihs ihu =>
      have hsu1 : cmp1 s u = .lt := canonicalBy_slash_lt hcanon1
      unfold canonicalBy at hcanon1
      rw [Bool.and_eq_true, Bool.and_eq_true] at hcanon1
      obtain ⟨⟨hcs, hcu⟩, _⟩ := hcanon1
      have ihs' := ihs hcs
      have ihu' := ihu hcu
      -- transportTree cmp2 s, u canonical-by-cmp2 (IH).
      -- f s ≠ f u: by g∘f = id.
      have hsu_ne : s ≠ u := by
        intro heq
        rw [heq] at hsu1
        rw [(h1.eq_iff u u).mpr rfl] at hsu1
        cases hsu1
      have hfs_ne : transportTree cmp2 s ≠ transportTree cmp2 u := by
        intro hfeq
        -- By transportTree_roundtrip cmp2 cmp1: g(f s) = s, g(f u) = u.
        have hgs := transportTree_roundtrip cmp2 cmp1 h2 h1 s hcs
        have hgu := transportTree_roundtrip cmp2 cmp1 h2 h1 u hcu
        rw [hfeq] at hgs
        rw [hgu] at hgs
        exact hsu_ne hgs.symm
      rw [transportTree_slash]
      -- slashTree cmp2 (f s) (f u) canonical (children canonical, order from cmp2).
      unfold slashTree
      cases hcmp2 : cmp2 (transportTree cmp2 s) (transportTree cmp2 u) with
      | lt =>
          unfold canonicalBy
          rw [ihs', ihu', hcmp2]
          rfl
      | eq =>
          have : transportTree cmp2 s = transportTree cmp2 u :=
            (h2.eq_iff _ _).mp hcmp2
          exact absurd this hfs_ne
      | gt =>
          unfold canonicalBy
          rw [ihs', ihu']
          have hus : cmp2 (transportTree cmp2 u) (transportTree cmp2 s) = .lt := by
            have hsw := h2.swap (transportTree cmp2 s) (transportTree cmp2 u)
            rw [hcmp2] at hsw
            cases hus_val : cmp2 (transportTree cmp2 u) (transportTree cmp2 s) with
            | lt => rfl
            | eq => rw [hus_val] at hsw; cases hsw
            | gt => rw [hus_val] at hsw; cases hsw
          rw [hus]
          rfl

end E213.Research.CmpIndependence

namespace E213.Research.CmpIndependence

open E213.Firmware E213.Firmware.Internal

/-- **Forward bijection**: RawBy cmp1 → RawBy cmp2 via transportTree. -/
def transportRawBy (cmp1 cmp2 : Tree → Tree → Ordering)
    (h1 : CmpProps cmp1) (h2 : CmpProps cmp2)
    (r : RawBy cmp1) : RawBy cmp2 :=
  ⟨transportTree cmp2 r.val,
   transportTree_canonical cmp1 cmp2 h1 h2 r.val r.property⟩

/-- **Bijection theorem**: transportRawBy 가 inverse 와 함께 bijection.
    f∘g = id, g∘f = id. -/
theorem transportRawBy_roundtrip
    (cmp1 cmp2 : Tree → Tree → Ordering)
    (h1 : CmpProps cmp1) (h2 : CmpProps cmp2)
    (r : RawBy cmp2) :
    transportRawBy cmp1 cmp2 h1 h2
      (transportRawBy cmp2 cmp1 h2 h1 r) = r := by
  apply Subtype.ext
  show transportTree cmp2 (transportTree cmp1 r.val) = r.val
  exact transportTree_roundtrip cmp1 cmp2 h1 h2 r.val r.property

/-- **Final**: RawBy cmp1 ≃ RawBy cmp2 (inverse via roundtrip).
    cmp-independence meta theorem 의 형식 closing. -/
theorem RawBy_bijection (cmp1 cmp2 : Tree → Tree → Ordering)
    (h1 : CmpProps cmp1) (h2 : CmpProps cmp2) :
    ∀ (r : RawBy cmp2),
        transportRawBy cmp1 cmp2 h1 h2
          (transportRawBy cmp2 cmp1 h2 h1 r) = r :=
  transportRawBy_roundtrip cmp1 cmp2 h1 h2

end E213.Research.CmpIndependence
