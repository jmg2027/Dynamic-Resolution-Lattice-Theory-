import E213.Hypervisor.Lens
import E213.Research.RawInitiality
import E213.Research.AxiomMinimality
import E213.Research.FoldStructured
import E213.Research.DepthParityNotFold

/-!
# Research.SemanticAtom: 213 = 의미 의 atom (formal hub)

Note 75 의 thesis 의 형식 화 hub.  이전 의 vague framing
들 (constructive subset, fold-structured, scale-invariance)
모두 이 thesis 의 specific aspect 임 명시.

## Thesis (Mingu, 2026-04-25)

> 의미 를 갖는 어떤 것 도 213 을 벗어날 수 없다.  213 이
> semantic atom 이다.  213 의 axiom 보다 더 원초적 부재.
> 모든 것 이 213 atom 의 내부 이자 표현 이자 경계.

## Formal layer

| Layer | Lean 형식 |
|-------|---------|
| Distinguishing framework abstraction | `HasDistinguishing` typeclass |
| Raw 가 instance | `Raw.instHasDistinguishing` |
| Universal morphism | `Raw.fold` (이미 있음) |
| Initial object | RawInitiality.lean (기존) |
| Strict minimum | AxiomMinimality.lean (4 cases) |

## Thesis 의 Lean 형식 부분

이 파일 은 `HasDistinguishing` typeclass 로 의미 framework 의
abstraction 명시 — Raw 가 이 abstraction 의 strict minimum
(AxiomMinimality 의 4 case 가 negative direction).
-/

namespace E213.Research.SemanticAtom

open E213.Firmware E213.Hypervisor

/-! ### HasDistinguishing typeclass — 의미 framework 의 abstraction

"의미 를 갖는 framework" 의 minimum requirements:
1. 두 distinguishable base elements (a ≠ b).
2. Combining operation (binary).
3. Combine 의 symmetry (swap-invariance) — slash 의 commutativity.

(3) 가 없으면 encoding artifact 가 결과 에 leak — Raw axiom 의
slash_comm.  따라서 의미 framework 의 part. -/

class HasDistinguishing (α : Type) where
  a : α
  b : α
  distinct : a ≠ b
  combine : α → α → α
  combine_sym : ∀ x y, combine x y = combine y x

end E213.Research.SemanticAtom

namespace E213.Research.SemanticAtom

open E213.Firmware E213.Hypervisor

/-! ### Raw 가 HasDistinguishing instance

가장 자명 한 instance: Raw 의 a, b, slash 자체 가 axiom 만족.
slash_comm 이 combine_sym 의 직접 보존. -/

instance : HasDistinguishing Raw where
  a := Raw.a
  b := Raw.b
  distinct := by decide
  combine x y := if h : x = y then x else Raw.slash x y h
  combine_sym x y := by
    by_cases h : x = y
    · simp [h]
    · simp [h, Ne.symm h]
      apply Raw.slash_comm

end E213.Research.SemanticAtom

namespace E213.Research.SemanticAtom

open E213.Firmware E213.Hypervisor

/-! ### Universal morphism: Raw → α (HasDistinguishing α)

`HasDistinguishing α` 의 instance 에 대해, Raw 가 unique
morphism 으로 embed.  fold 가 universal morphism — Raw 가
"distinguishing framework" category 의 initial object.

(즉 213 의 axiom 이 *모든* 의미 framework 의 minimum.) -/

/-- Universal morphism Raw → α via fold. -/
def universalMorphism (α : Type) [d : HasDistinguishing α] : Raw → α :=
  Raw.fold d.a d.b d.combine

/-- Universal morphism preserves a. -/
theorem universalMorphism_a (α : Type) [d : HasDistinguishing α] :
    universalMorphism α Raw.a = d.a := rfl

/-- Universal morphism preserves b. -/
theorem universalMorphism_b (α : Type) [d : HasDistinguishing α] :
    universalMorphism α Raw.b = d.b := rfl

/-- Universal morphism preserves slash via fold_slash. -/
theorem universalMorphism_slash (α : Type) [d : HasDistinguishing α]
    (x y : Raw) (h : x ≠ y) :
    universalMorphism α (Raw.slash x y h)
      = d.combine (universalMorphism α x) (universalMorphism α y) := by
  unfold universalMorphism
  apply Raw.fold_slash _ _ _ d.combine_sym

end E213.Research.SemanticAtom

namespace E213.Research.SemanticAtom

open E213.Firmware E213.Hypervisor

/-! ### Lens 가 HasDistinguishing 의 specific instance

Lens α 의 view 는 HasDistinguishing α 의 morphism — 즉 Lens
는 의미 framework 의 instance 의 specific 형태.  Raw 가 모든
Lens 의 carrier (universal). -/

/-- Lens 가 HasDistinguishing 의 instance — base 의 distinctness
    + combine 의 swap-sym 을 hypothesis 로 받음.  일반 Lens 는
    constLens 같은 degenerate case 가 distinguishing 부재 (base_a
    = base_b) 가 가능 하므로, distinguishing 보존 Lens 만 instance.

    이 partial functoriality 가 "의미 의 atom 은 Raw, Lens 는
    그 위 의 representation" 의 형식 표현. -/
def lensToHasDistinguishing {α : Type} (L : Lens α)
    (h_distinct : L.base_a ≠ L.base_b)
    (h_sym : ∀ u v, L.combine u v = L.combine v u) :
    HasDistinguishing α where
  a := L.base_a
  b := L.base_b
  distinct := h_distinct
  combine := L.combine
  combine_sym := h_sym

end E213.Research.SemanticAtom

namespace E213.Research.SemanticAtom

open E213.Firmware E213.Hypervisor

/-! ### `Prop` 이 `HasDistinguishing` instance

Lean 의 `Prop` type 도 `HasDistinguishing` instance 가 될 수
있다 — `True ≠ False` + commutative connective.  이걸 형식
화 하면 `universalMorphism Prop : Raw → Prop` 이 자동 생성
(fold via the chosen connective).

**구성:**
- `True`, `False`: 두 distinguishable base.
- `propXor` (= `(P ∨ Q) ∧ ¬(P ∧ Q)`): commutative combine.
- 다른 commutative connective (Iff, And, Or) 도 instance 가능
  — 아래 alternative 참조.

**의의 (note 76 분석):**

Lens 의 view 가 일반 적 으로 Raw → α (α : Type).  α = Prop
case 가 특수 한 의의 — thesis 가 자기 의 truth value 를
framework 안 의 universal morphism 으로 결정.  이건 framework
의 self-coverage 의 부분 적 형식 — "thesis 의 logical 평가
가 외부 metatheory 가 아니라 framework 안 derivation".

(이것 이 모든 Prop 을 cover 한다 는 의미 가 아님 — Prop 이
HasDistinguishing 의 *하나 의* instance 일 수 있음 만.  자세
한 한계 는 note 76 §"Limits".)
-/

/-- Xor on Prop — commutative + distinguishing 보존 connective. -/
def propXor (P Q : Prop) : Prop := (P ∨ Q) ∧ ¬(P ∧ Q)

theorem propXor_comm (P Q : Prop) : propXor P Q = propXor Q P := by
  unfold propXor
  apply propext
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨h1.symm, ?_⟩
    intro h; exact h2 h.symm
  · rintro ⟨h1, h2⟩
    refine ⟨h1.symm, ?_⟩
    intro h; exact h2 h.symm

theorem true_ne_false : (True : Prop) ≠ False := by
  intro h; exact h.mp trivial

/-- **Prop 이 distinguishing-framework category 의 object**.
    `True ≠ False` + `propXor` (= Raw.slash 의 boolean parallel). -/
def propAsDistinguishing : HasDistinguishing Prop where
  a := True
  b := False
  distinct := true_ne_false
  combine := propXor
  combine_sym := propXor_comm

/-- Universal morphism Raw → Prop via `propAsDistinguishing`.
    Prop 이 HasDistinguishing instance 인 specific case 의
    fold-derived 함수. -/
def canonicalTruthMap : Raw → Prop :=
  @universalMorphism Prop propAsDistinguishing

/-- canonicalTruthMap a = True. -/
theorem canonicalTruthMap_a : canonicalTruthMap Raw.a = True :=
  @universalMorphism_a Prop propAsDistinguishing

/-- canonicalTruthMap b = False. -/
theorem canonicalTruthMap_b : canonicalTruthMap Raw.b = False :=
  @universalMorphism_b Prop propAsDistinguishing

/-- canonicalTruthMap (slash x y h) = propXor (... x) (... y). -/
theorem canonicalTruthMap_slash (x y : Raw) (h : x ≠ y) :
    canonicalTruthMap (Raw.slash x y h)
      = propXor (canonicalTruthMap x) (canonicalTruthMap y) :=
  @universalMorphism_slash Prop propAsDistinguishing x y h

end E213.Research.SemanticAtom

namespace E213.Research.SemanticAtom

open E213.Firmware E213.Hypervisor

/-! ### Alternative connective: `Iff`

Prop 이 *하나 의* HasDistinguishing instance 만 가지는 게 아님
— 다른 commutative connective 도 instance.  여기 서 `Iff`
(↔, "same truth value") 의 instance 를 보여서 specific Xor
선택 에 의존 하지 않음 demonstrate.

(이게 framework 의 self-coverage 가 *어떤 specific connective*
에 의존 하지 않음 — 단지 `True ≠ False` + commutative combine
의 minimum 구조 에 의존 한다는 sober claim.) -/

theorem iff_comm_eq (P Q : Prop) : (P ↔ Q) = (Q ↔ P) := by
  apply propext
  exact ⟨Iff.symm, Iff.symm⟩

/-- Prop 의 Iff-based instance.  `True ↔ False = False` (distinguishing
    보존), `True ↔ True = True`, `False ↔ False = True`. -/
def propAsDistinguishingIff : HasDistinguishing Prop where
  a := True
  b := False
  distinct := true_ne_false
  combine := Iff
  combine_sym := iff_comm_eq

/-- Iff-based universal morphism — Xor instance 와 *다른* fold
    함수 를 produce (당연 — fold rule 이 다름).  Prop instance
    의 non-uniqueness 보임. -/
def canonicalIffMap : Raw → Prop :=
  @universalMorphism Prop propAsDistinguishingIff

end E213.Research.SemanticAtom

namespace E213.Research.SemanticAtom

open E213.Firmware E213.Hypervisor
open E213.Research.FoldStructured

/-! ### Negative direction: Lens-expressibility 의 boundary

§1.1 (formal core) 의 dual.  `HasDistinguishing` typeclass 가
"의미 framework 의 abstraction" 의 positive form 이라면, 다음
은 negative form: **framework 안 표현 부재 한 함수 의 존재**.

이미 `Research/{NoDepthParity, DepthParityNotFold,
SlashCharNotFold}.lean` 에 specific instance 들 형식 화 됨.
여기 서 통합 statement 명시 — Lens-expressibility 가 자명 하지
않은 boundary (모든 Raw → α 함수 가 Lens-expressible 인 게
아님).

Note 77 의 통합 분석. -/

/-- **Lens-expressible** 의 정확 한 정의: f 가 어떤 Lens L 의
    view (with combine 의 swap-symmetry 가정). -/
def IsLensExpressible {α : Type} (f : Raw → α) : Prop :=
  ∃ L : Lens α, (∀ u v, L.combine u v = L.combine v u) ∧
                (∀ r, L.view r = f r)

/-- IsLensExpressible ↔ FoldStructured.  FoldStructured.lean
    의 결과 의 wrapping. -/
theorem isLensExpressible_iff_foldStructured {α : Type} (f : Raw → α) :
    IsLensExpressible f ↔ FoldStructured f := by
  unfold IsLensExpressible
  constructor
  · rintro ⟨L, hsym, hview⟩
    have h : L.view = f := funext hview
    rw [← h]
    exact lens_view_fold_structured L hsym
  · intro hfs
    obtain ⟨L, hsym, hview⟩ := fold_structured_lens_expressible f hfs
    exact ⟨L, hsym, fun r => congrFun hview r⟩

/-- **Negative existence**: ∃ f : Raw → Bool, f 가 Lens-expressible
    이 아님.  의미 atom thesis 의 boundary 의 직접 evidence. -/
theorem exists_non_lens_expressible :
    ∃ f : Raw → Bool, ¬ IsLensExpressible f := by
  refine ⟨E213.Research.DepthParityNotFold.depthParityFn, ?_⟩
  rw [isLensExpressible_iff_foldStructured]
  exact E213.Research.DepthParityNotFold.depthParityFn_not_fold_structured

end E213.Research.SemanticAtom

namespace E213.Research.SemanticAtom

open E213.Firmware E213.Hypervisor
open E213.Research.RawInitiality

/-! ### Universal property of `HasDistinguishing` category

`Lens.initiality` (RawInitiality.lean) 의 HasDistinguishing-level
재진술.  Raw 가 distinguishing-framework category 의 *initial
object* 의 명시 적 ∃! statement. -/

/-- **Universal morphism uniqueness**: HasDistinguishing α 의
    instance 에 대해, distinguishing-preserving 함수 Raw → α
    가 정확히 `universalMorphism α`. -/
theorem universalMorphism_unique (α : Type) [d : HasDistinguishing α]
    (f : Raw → α)
    (ha : f Raw.a = d.a)
    (hb : f Raw.b = d.b)
    (hslash : ∀ (x y : Raw) (h : x ≠ y),
              f (Raw.slash x y h) = d.combine (f x) (f y)) :
    ∀ r : Raw, f r = universalMorphism α r := by
  intro r
  exact Lens.view_unique
    (⟨d.a, d.b, d.combine⟩ : Lens α) d.combine_sym f ha hb hslash r

/-- **Raw 가 HasDistinguishing-category 의 initial object**:
    임의 instance α 에 대해, distinguishing-preserving 함수
    Raw → α 가 *unique 하게* 존재 (= `universalMorphism α`).
    이게 "213 axiom 이 모든 의미 framework 의 minimum" 의
    categorical 명시.  (∃! Lean 4 core syntax 부재, explicit
    existence + uniqueness conjunction 형식.) -/
theorem raw_initial (α : Type) [d : HasDistinguishing α] :
    ∃ f : Raw → α,
      (f Raw.a = d.a) ∧
      (f Raw.b = d.b) ∧
      (∀ (x y : Raw) (h : x ≠ y),
        f (Raw.slash x y h) = d.combine (f x) (f y)) ∧
      (∀ g : Raw → α,
        g Raw.a = d.a →
        g Raw.b = d.b →
        (∀ (x y : Raw) (h : x ≠ y),
          g (Raw.slash x y h) = d.combine (g x) (g y)) →
        g = f) := by
  refine ⟨universalMorphism α, ?_, ?_, ?_, ?_⟩
  · exact universalMorphism_a α
  · exact universalMorphism_b α
  · intro x y h; exact universalMorphism_slash α x y h
  · intro g hga hgb hgslash
    funext r
    exact universalMorphism_unique α g hga hgb hgslash r

end E213.Research.SemanticAtom
