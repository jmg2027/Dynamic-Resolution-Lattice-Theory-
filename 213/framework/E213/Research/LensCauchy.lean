import E213.Research.UniversalQuotLens

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
