import E213.Research.UniversalQuotLens
import E213.Research.IndexedJoinLens

/-!
# Research.LensCauchy: 213 의 Cauchy completeness 환원

Mingu 제안 (2026-04-25):
- ε → "Lens L 의 해상도".
- Cauchy → "임의 fine Lens L 에 대해 sequence tail 이 L-class 로
  collapse".
- Completeness → universalLens 로 limit slash-cong 정의.

## 정의

**Lens-Cauchy**: sequence xs : ℕ → Raw 가 Lens L 에 대해
Cauchy iff ∃ N, ∀ m n ≥ N, L.equiv (xs m) (xs n).

**Family-Cauchy**: directed family D 의 모든 L 에 대해 Cauchy.

## 핵심 통찰

- Limit class = sequence 의 eventually-constant L-class.
- Completeness = limit class 의 well-defined 성 + universalLens
  로 capture.
- 외부 metric / topology 부재.  Lens lattice 만 사용.

이 파일 은 framework 시작 — 본격 ℝ-construction 은 별도.
-/

namespace E213.Research.LensCauchy

open E213.Firmware E213.Hypervisor

/-- **Lens-Cauchy**: 단일 Lens L 에 대한 Cauchy. -/
def LensCauchy {α : Type} (L : Lens α) (xs : Nat → Raw) : Prop :=
  ∃ N, ∀ m n, m ≥ N → n ≥ N → L.equiv (xs m) (xs n)

/-- **Eventually-constant L-class**: tail 이 single L-class 로
    collapse. -/
def EventuallyClass {α : Type} (L : Lens α) (xs : Nat → Raw)
    (c : α) : Prop :=
  ∃ N, ∀ n, n ≥ N → L.view (xs n) = c

/-- **Cauchy ↔ EventuallyClass**: 단일 Lens 에 대해 두 정의 동치. -/
theorem cauchy_iff_eventually_class {α : Type} (L : Lens α)
    (xs : Nat → Raw) :
    LensCauchy L xs ↔ ∃ c, EventuallyClass L xs c := by
  constructor
  · intro ⟨N, h⟩
    refine ⟨L.view (xs N), N, ?_⟩
    intro n hn
    exact h n N hn (Nat.le_refl N)
  · intro ⟨c, N, h⟩
    refine ⟨N, ?_⟩
    intro m n hm hn
    show L.view (xs m) = L.view (xs n)
    rw [h m hm, h n hn]

/-- Limit class 의 uniqueness: 두 EventuallyClass 가 같음. -/
theorem eventually_class_unique {α : Type} (L : Lens α) (xs : Nat → Raw)
    (c c' : α) (h : EventuallyClass L xs c) (h' : EventuallyClass L xs c') :
    c = c' := by
  obtain ⟨N, hN⟩ := h
  obtain ⟨N', hN'⟩ := h'
  let M := max N N'
  have hMN : M ≥ N := Nat.le_max_left N N'
  have hMN' : M ≥ N' := Nat.le_max_right N N'
  rw [← hN M hMN, hN' M hMN']

end E213.Research.LensCauchy

namespace E213.Research.LensCauchy

open E213.Firmware E213.Hypervisor

/-- **Cauchy witness 구조**: explicit N + Cauchy 성질.
    Constructive (Classical.choice 부재). -/
structure CauchyData {α : Type} (L : Lens α) (xs : Nat → Raw) where
  N : Nat
  cauchy : ∀ m n, m ≥ N → n ≥ N → L.equiv (xs m) (xs n)

/-- **Limit class**: Cauchy data 로 부터 limit value 직접 계산.
    Witness N 의 view 가 limit (Cauchy 성으로 N 선택 무관). -/
def limitClass {α : Type} {L : Lens α} {xs : Nat → Raw}
    (cd : CauchyData L xs) : α := L.view (xs cd.N)

/-- **Limit class 의 well-definedness**: tail elements 모두
    limit value 와 같은 L.view. -/
theorem limitClass_eq_tail {α : Type} (L : Lens α) (xs : Nat → Raw)
    (cd : CauchyData L xs) (n : Nat) (hn : n ≥ cd.N) :
    L.view (xs n) = limitClass cd := by
  unfold limitClass
  exact cd.cauchy n cd.N hn (Nat.le_refl cd.N)

/-- **Cauchy → ∃ limit class** (existential form).  CauchyData 의
    proposition 형태 이지만 자동 추출 가능 — `Cauchy → ∃ N witness`
    → CauchyData. -/
theorem cauchy_data_of {α : Type} (L : Lens α) (xs : Nat → Raw)
    (h : LensCauchy L xs) :
    ∃ cd : CauchyData L xs, True := by
  obtain ⟨N, hN⟩ := h
  exact ⟨⟨N, hN⟩, trivial⟩

end E213.Research.LensCauchy

namespace E213.Research.LensCauchy

open E213.Firmware E213.Hypervisor

/-- **Family-Cauchy**: 모든 (F i).2 에 대해 Cauchy. -/
def FamilyCauchy {ι : Type} (F : ι → (α : Type) × Lens α)
    (xs : Nat → Raw) : Prop :=
  ∀ i, LensCauchy (F i).2 xs

/-- **Limit assignment 구조**: 각 i 에 explicit Cauchy witness. -/
structure LimitAssignment {ι : Type} (F : ι → (α : Type) × Lens α)
    (xs : Nat → Raw) where
  data : ∀ i, CauchyData (F i).2 xs

/-- Limit value 추출 — 각 i 의 limit class. -/
def LimitAssignment.limit {ι : Type} {F : ι → (α : Type) × Lens α}
    {xs : Nat → Raw} (la : LimitAssignment F xs) (i : ι) : (F i).1 :=
  limitClass (la.data i)

end E213.Research.LensCauchy

namespace E213.Research.LensCauchy

open E213.Firmware E213.Hypervisor E213.Research.IndexedJoinLens

/-- **Pointwise limit match**: family-Cauchy seq 의 limit
    assignment 가 iProdLens F 의 view 와 pointwise 일치. -/
theorem pointwise_limit_match {ι : Type} (F : ι → (α : Type) × Lens α)
    (xs : Nat → Raw)
    (hAllSym : ∀ i (u v : (F i).1),
                (F i).2.combine u v = (F i).2.combine v u)
    (la : LimitAssignment F xs) (i : ι) :
    ∃ N, ∀ n, n ≥ N → (iProdLens F).view (xs n) i = la.limit i := by
  refine ⟨(la.data i).N, ?_⟩
  intro n hn
  rw [iProdLens_view F hAllSym (xs n)]
  exact limitClass_eq_tail (F i).2 xs (la.data i) n hn

end E213.Research.LensCauchy

namespace E213.Research.LensCauchy

open E213.Firmware E213.Hypervisor E213.Research.UniversalQuotLens

/-- **Tail congruence**: sequence xs 의 tail 부터 시작 하는
    minimum slash-cong.  모든 tail elements (xs m, xs k) for m, k
    ≥ N 가 single class 로 collapse. -/
inductive TailCong (xs : Nat → Raw) (N : Nat) : Raw → Raw → Prop where
  | tail_eq (m k : Nat) (hm : m ≥ N) (hk : k ≥ N) :
      TailCong xs N (xs m) (xs k)
  | refl (r : Raw) : TailCong xs N r r
  | symm : TailCong xs N r r' → TailCong xs N r' r
  | trans :
      TailCong xs N r r' → TailCong xs N r' r'' → TailCong xs N r r''
  | slash_cong (hxy : x ≠ y) (hx'y' : x' ≠ y') :
      TailCong xs N x x' → TailCong xs N y y' →
      TailCong xs N (Raw.slash x y hxy) (Raw.slash x' y' hx'y')

/-- TailCong 은 slash-cong (slash_cong constructor 직접). -/
theorem tailCong_slash_cong (xs : Nat → Raw) (N : Nat)
    (x x' y y' : Raw) (hxy : x ≠ y) (hx'y' : x' ≠ y')
    (hxx' : TailCong xs N x x') (hyy' : TailCong xs N y y') :
    TailCong xs N (Raw.slash x y hxy) (Raw.slash x' y' hx'y') :=
  TailCong.slash_cong hxy hx'y' hxx' hyy'

/-- **Limit Lens**: TailCong 의 universalLens 가 sequence 의 limit
    Lens.  Q37.3 + Cauchy completeness 의 통합. -/
def limitLens (xs : Nat → Raw) (N : Nat) : Lens (Raw → Prop) :=
  universalLens (TailCong xs N)

/-- **Limit Lens 의 kernel = TailCong**.  universalLens 의 직접
    귀결. -/
theorem limitLens_kernel (xs : Nat → Raw) (N : Nat) (r r' : Raw) :
    (limitLens xs N).view r = (limitLens xs N).view r'
      ↔ TailCong xs N r r' := by
  apply universalLens_kernel_eq_E
  · exact fun x => TailCong.refl x
  · exact fun _ _ h => TailCong.symm h
  · exact fun _ _ _ h1 h2 => TailCong.trans h1 h2
  · exact fun _ _ _ _ hxy hx'y' h1 h2 =>
      TailCong.slash_cong hxy hx'y' h1 h2

/-- **Tail collapse**: 모든 tail elements (xs m, xs k) (m, k ≥ N)
    가 limitLens 에서 single class.  Cauchy completeness 의 핵심
    표현. -/
theorem limitLens_tail_collapse (xs : Nat → Raw) (N : Nat)
    (m k : Nat) (hm : m ≥ N) (hk : k ≥ N) :
    (limitLens xs N).view (xs m) = (limitLens xs N).view (xs k) :=
  (limitLens_kernel xs N (xs m) (xs k)).mpr (TailCong.tail_eq m k hm hk)

/-- TailCong ⊆ N.equiv (helper for universal property). -/
private theorem tailCong_implies_equiv {α : Type} (N : Lens α)
    (hNsym : ∀ u v, N.combine u v = N.combine v u)
    (xs : Nat → Raw) (M : Nat)
    (hCollapse : ∀ m k, m ≥ M → k ≥ M → N.equiv (xs m) (xs k))
    (r r' : Raw) (h : TailCong xs M r r') :
    N.equiv r r' := by
  induction h with
  | tail_eq m k hm hk => exact hCollapse m k hm hk
  | refl x => exact rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2
  | slash_cong hxy hx'y' _ _ ih1 ih2 =>
      exact E213.Research.KernelCongruence.Lens.equiv_slash_congruence
        N hNsym _ _ _ _ hxy hx'y' ih1 ih2

/-- **limitLens 의 universal property (least tail-collapsing Lens)**:
    임의 Lens N (combine sym) 가 tail 을 collapse 하면, limitLens 가
    N 을 refine.  즉 limitLens 가 가장 finer 한 tail-collapsing
    Lens — Cauchy seq 의 limit Lens 의 universal characterization. -/
theorem limitLens_is_least {α : Type} (N : Lens α)
    (hNsym : ∀ u v, N.combine u v = N.combine v u)
    (xs : Nat → Raw) (M : Nat)
    (hCollapse : ∀ m k, m ≥ M → k ≥ M → N.equiv (xs m) (xs k)) :
    (limitLens xs M).refines N := by
  intro r r' h
  have hTC : TailCong xs M r r' := (limitLens_kernel xs M r r').mp h
  exact tailCong_implies_equiv N hNsym xs M hCollapse r r' hTC

end E213.Research.LensCauchy
