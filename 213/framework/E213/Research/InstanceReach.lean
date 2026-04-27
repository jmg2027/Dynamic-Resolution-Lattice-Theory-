import E213.Research.SemanticAtom

/-!
# Research.InstanceReach: universalMorphism 의 image 의 boundary

`SemanticAtom.lean` 의 `universalMorphism α : Raw → α` 가
HasDistinguishing instance α 의 morphism.  이 image 가 *항상*
α 와 같은 가? — 답: **아님**.  α 의 carrier 가 image 보다 더
클 수 있음.

## 의의

의미 atom thesis 의 sharpening:

> Raw 가 모든 distinguishing-framework instance 의 *generator*
> (image 가 distinguishing-closed sub-instance).  하지만 instance
> 의 carrier 가 image 보다 *strict 클* 수 있음 — framework 의
> reach 와 carrier 의 분리.

즉 의미 atom 이 generator 의 minimum 이고, instance 가 그 위
"unreachable" element 를 carry 가능.  이게 framework 의 *reach
boundary* 의 명시.

## Witness

`Fin 3` with `a := 0, b := 1, combine := λ _ _, 0`:
- reach = {0, 1} (Raw 로 부터 image).
- carrier = {0, 1, 2}.
- 2 ∉ image — strict subset.

Note 80 분석.
-/

namespace E213.Research.InstanceReach

open E213.Firmware E213.Hypervisor
open E213.Research.SemanticAtom

/-! ### Witness: Fin 3 의 trivial-combine instance -/

instance fin3HasDistinguishing : HasDistinguishing (Fin 3) where
  a := 0
  b := 1
  distinct := by decide
  combine _ _ := 0
  combine_sym _ _ := rfl

/-- Image 의 forward closure: universalMorphism (Fin 3) 의 결과
    가 항상 0 또는 1 (combine 이 항상 0). -/
theorem fin3_image_in_01 (r : Raw) :
    universalMorphism (Fin 3) r = 0 ∨ universalMorphism (Fin 3) r = 1 := by
  induction r using Raw.rec with
  | a => left; exact universalMorphism_a (Fin 3)
  | b => right; exact universalMorphism_b (Fin 3)
  | slash x y h _ _ =>
      left
      rw [universalMorphism_slash (Fin 3) x y h]
      rfl

end E213.Research.InstanceReach

namespace E213.Research.InstanceReach

open E213.Firmware E213.Hypervisor
open E213.Research.SemanticAtom

/-- **Image 의 strict subset**: Fin 3 의 element 2 가 universalMorphism
    의 image 외부.  framework 의 reach 와 carrier 의 분리 의 명시
    적 witness. -/
theorem fin3_image_strict :
    ∃ x : Fin 3, ¬ ∃ r : Raw, universalMorphism (Fin 3) r = x := by
  refine ⟨2, ?_⟩
  intro ⟨r, hr⟩
  rcases fin3_image_in_01 r with h | h
  · rw [h] at hr; exact absurd hr (by decide)
  · rw [h] at hr; exact absurd hr (by decide)

end E213.Research.InstanceReach

namespace E213.Research.InstanceReach

open E213.Firmware E213.Hypervisor
open E213.Research.SemanticAtom

/-! ### Dual: Bool instance 가 surjective

`Fin 3` 가 non-surjective 의 witness.  `Bool` 은 *항상* surjective
— a, b 의 두 base 만 으로 carrier 전체 커버.  reach = carrier
의 instance 의 example. -/

instance boolHasDistinguishing : HasDistinguishing Bool where
  a := true
  b := false
  distinct := by decide
  combine := and
  combine_sym := Bool.and_comm

/-- Bool instance 의 universalMorphism 이 surjective. -/
theorem bool_image_surjective :
    ∀ b : Bool, ∃ r : Raw, universalMorphism Bool r = b := by
  intro b
  cases b with
  | true => exact ⟨Raw.a, universalMorphism_a Bool⟩
  | false => exact ⟨Raw.b, universalMorphism_b Bool⟩

end E213.Research.InstanceReach

namespace E213.Research.InstanceReach

open E213.Firmware E213.Hypervisor
open E213.Research.SemanticAtom

/-! ### Image 의 minimum 성질 (closure under bases) -/

/-- Image 가 항상 d.a 를 포함. -/
theorem image_contains_a (α : Type) [d : HasDistinguishing α] :
    ∃ r : Raw, universalMorphism α r = d.a :=
  ⟨Raw.a, universalMorphism_a α⟩

/-- Image 가 항상 d.b 를 포함. -/
theorem image_contains_b (α : Type) [d : HasDistinguishing α] :
    ∃ r : Raw, universalMorphism α r = d.b :=
  ⟨Raw.b, universalMorphism_b α⟩

/-- Distinct image elements 의 combine 도 image — Raw.slash 의
    direct application. -/
theorem image_closed_under_distinct_combine (α : Type) [d : HasDistinguishing α]
    (rx ry : Raw) (h : rx ≠ ry) :
    ∃ r : Raw,
      universalMorphism α r
        = d.combine (universalMorphism α rx) (universalMorphism α ry) :=
  ⟨Raw.slash rx ry h, universalMorphism_slash α rx ry h⟩

end E213.Research.InstanceReach

namespace E213.Research.InstanceReach

open E213.Firmware E213.Hypervisor
open E213.Research.SemanticAtom

/-! ### Infinite surjective: Nat with addition

Bool 이 finite surjective.  Fin 3 (constant combine) 이 finite
non-surjective.  Nat with addition: **infinite surjective** —
모든 Nat 가 image, carrier 무한.

`a := 0`, `b := 1`, `combine := (· + ·)`.  combine_sym 자명
(`Nat.add_comm`).

Witness: r n := slash (r (n-1)) Raw.b _ for n ≥ 1, r 0 := Raw.a.
universalMorphism = n by induction. -/

instance natHasDistinguishing : HasDistinguishing Nat where
  a := 0
  b := 1
  distinct := by decide
  combine := (· + ·)
  combine_sym := Nat.add_comm

end E213.Research.InstanceReach

namespace E213.Research.InstanceReach

open E213.Firmware E213.Hypervisor
open E213.Research.SemanticAtom

/-- Concrete witnesses for small Nat values — Raw.a, Raw.b cover
    {0, 1}, slash 가 더 큰 element generate. -/
theorem nat_image_zero : ∃ r : Raw, universalMorphism Nat r = 0 :=
  ⟨Raw.a, universalMorphism_a Nat⟩

theorem nat_image_one : ∃ r : Raw, universalMorphism Nat r = 1 :=
  ⟨Raw.b, universalMorphism_b Nat⟩

/-- 0 + 1 = 1 via slash a b. -/
theorem nat_image_via_slash_ab :
    universalMorphism Nat (Raw.slash Raw.a Raw.b (by decide)) = 1 := by
  rw [universalMorphism_slash Nat Raw.a Raw.b (by decide)]
  rw [universalMorphism_a Nat, universalMorphism_b Nat]
  rfl

end E213.Research.InstanceReach

namespace E213.Research.InstanceReach

open E213.Firmware E213.Hypervisor
open E213.Research.SemanticAtom

/-! ### Nat surjective: 완전 증명

`natHasDistinguishing` 가 surjective — ∀ n : Nat, ∃ r : Raw,
universalMorphism Nat r = n.

Witness construction: induction on n.
- n = 0: r = Raw.a.
- n ≥ 1: r n := Raw.slash (Raw.a) (witness for n-1 ≥ 1) + base
  case Raw.b for n = 1.

Trick: induction with strong invariant — r n ≠ Raw.a for n ≥ 1
+ universalMorphism r n = n.  Then slash Raw.a (r n) (a ≠ rn).
-/

/-- Helper: Raw.slash 의 결과 가 Raw.a 와 다름 (depth-based proof). -/
private theorem slash_ne_a (x y : Raw) (h : x ≠ y) :
    Raw.slash x y h ≠ Raw.a := by
  intro heq
  have hview := congrArg Lens.depth.view heq
  have hslash : Lens.depth.view (Raw.slash x y h)
                = 1 + max (Lens.depth.view x) (Lens.depth.view y) := by
    apply Raw.fold_slash
    intro u v
    show 1 + max u v = 1 + max v u
    rw [Nat.max_comm]
  rw [hslash] at hview
  show False
  have h_a : Lens.depth.view Raw.a = 0 := rfl
  rw [h_a] at hview
  omega

end E213.Research.InstanceReach

namespace E213.Research.InstanceReach

open E213.Firmware E213.Hypervisor
open E213.Research.SemanticAtom

/-! ### natWitness construction note

각 Nat n 의 explicit Raw witness:
- r 0 := Raw.a (universalMorphism = 0).
- r (n+1) := slash Raw.b (r n) (proof Raw.b ≠ r n).
  → universalMorphism = 1 + n.
Need: ∀ n, r n ≠ Raw.b.  By induction:
- r 0 = Raw.a ≠ Raw.b (decide).
- r (n+1) = slash _ _ _ ≠ Raw.b (slash_ne_b 로 proof).
-/

/-- Helper: Raw.slash 의 결과 가 Raw.b 와 다름. -/
private theorem slash_ne_b (x y : Raw) (h : x ≠ y) :
    Raw.slash x y h ≠ Raw.b := by
  intro heq
  have hview := congrArg Lens.depth.view heq
  have hslash : Lens.depth.view (Raw.slash x y h)
                = 1 + max (Lens.depth.view x) (Lens.depth.view y) := by
    apply Raw.fold_slash
    intro u v
    show 1 + max u v = 1 + max v u
    rw [Nat.max_comm]
  rw [hslash] at hview
  show False
  have h_b : Lens.depth.view Raw.b = 0 := rfl
  rw [h_b] at hview
  omega

end E213.Research.InstanceReach

namespace E213.Research.InstanceReach

open E213.Firmware E213.Hypervisor
open E213.Research.SemanticAtom

/-- Helper: combined `r ≠ Raw.b` for both Raw.a and slash forms. -/
private theorem natWitness_ne_b_helper (r : Raw)
    (h : r = Raw.a ∨ ∃ x y h', r = Raw.slash x y h') :
    r ≠ Raw.b := by
  rcases h with hra | ⟨x, y, h', hsl⟩
  · subst hra; decide
  · subst hsl; exact slash_ne_b x y h'

end E213.Research.InstanceReach

namespace E213.Research.InstanceReach

open E213.Firmware E213.Hypervisor
open E213.Research.SemanticAtom

/-- **Nat surjective with form invariant**: 모든 n 에 대해 explicit
    Raw witness 의 form 도 동시에 induct (form invariant 가 induction
    step 에서 사용). -/
theorem nat_surjective_with_form : ∀ n : Nat, ∃ r : Raw,
    universalMorphism Nat r = n ∧
    (r = Raw.a ∨ ∃ x y h, r = Raw.slash x y h) := by
  intro n
  induction n with
  | zero => exact ⟨Raw.a, universalMorphism_a Nat, Or.inl rfl⟩
  | succ n ih =>
      obtain ⟨r, hr_view, hr_form⟩ := ih
      have h_ne : r ≠ Raw.b := natWitness_ne_b_helper r hr_form
      have h_b_ne_r : Raw.b ≠ r := Ne.symm h_ne
      refine ⟨Raw.slash Raw.b r h_b_ne_r, ?_, Or.inr ⟨Raw.b, r, h_b_ne_r, rfl⟩⟩
      rw [universalMorphism_slash Nat Raw.b r h_b_ne_r,
          universalMorphism_b Nat, hr_view]
      show 1 + n = n + 1
      exact Nat.add_comm 1 n

/-- **Main result**: Nat instance 의 universalMorphism 이 surjective. -/
theorem nat_image_surjective :
    ∀ n : Nat, ∃ r : Raw, universalMorphism Nat r = n := by
  intro n
  obtain ⟨r, hview, _⟩ := nat_surjective_with_form n
  exact ⟨r, hview⟩

end E213.Research.InstanceReach

namespace E213.Research.InstanceReach

open E213.Firmware E213.Hypervisor
open E213.Research.SemanticAtom

/-! ### Int with addition: infinite non-surjective

Bool finite surj, Fin 3 finite non-surj, Nat infinite surj.
Int with addition: **infinite non-surjective** — Nat ⊊ Int 의
positive part 만 reach, negative numbers unreachable (combine
= + 가 항상 비감 소).

이게 infinite 의 cardinality 가 surjective 부재 의 explicit
witness — image 가 *strict* infinite subset. -/

instance intHasDistinguishing : HasDistinguishing Int where
  a := 0
  b := 1
  distinct := by decide
  combine := (· + ·)
  combine_sym := Int.add_comm

/-- Image 의 forward closure: universalMorphism Int 의 결과 가
    항상 ≥ 0. -/
theorem int_image_nonneg (r : Raw) : 0 ≤ universalMorphism Int r := by
  induction r using Raw.rec with
  | a =>
      rw [universalMorphism_a Int]
      exact Int.le_refl 0
  | b =>
      rw [universalMorphism_b Int]
      decide
  | slash x y h ihx ihy =>
      rw [universalMorphism_slash Int x y h]
      exact Int.add_nonneg ihx ihy

/-- **Image 의 strict subset (infinite case)**: -1 ∈ Int 가
    universalMorphism 의 image 외부.  infinite carrier 의 non-
    surjective witness. -/
theorem int_image_strict :
    ∃ x : Int, ¬ ∃ r : Raw, universalMorphism Int r = x := by
  refine ⟨-1, ?_⟩
  intro ⟨r, hr⟩
  have h_nonneg : 0 ≤ universalMorphism Int r := int_image_nonneg r
  rw [hr] at h_nonneg
  exact absurd h_nonneg (by decide)

end E213.Research.InstanceReach
