import E213.Firmware.Raw
import E213.Hypervisor.Lens

/-!
# Research.RawInitiality: Raw 는 Raw-algebra 범주의 초기 객체

Note 32 claim 의 형식화.  임의의 Lens `L : Lens α` 에 대해,
`Raw → α` 의 homomorphism 이 존재하고 (= `L.view`), 유일함.

## 의의

Note 31 §7 정리 후보 ("모든 mathematical structure 는 최소
2 상호 필요 요소") 의 **엄밀 절반** — Raw-algebra 로 한정한
경우의 universal property.

존재성은 `Lens.view` 자체.  이 파일은 **유일성** 기계 검증.

## §1. 유일성 정리 (Lens.view_unique)

임의의 함수 f : Raw → α 가 Lens 의 homomorphism 조건을 만족
하면 f = Lens.view.
-/

namespace E213.Research.RawInitiality

open E213.Firmware E213.Hypervisor

/-- **Raw-algebra homomorphism 의 유일성 (commutative combine).**

    임의의 `f : Raw → α` 가 다음을 만족하면 f = L.view:
    - L.combine 이 commutative.
    - `f Raw.a = L.base_a`
    - `f Raw.b = L.base_b`
    - `f (Raw.slash x y h) = L.combine (f x) (f y)` (모든 x, y, h)

    즉 Raw 는 commutative Lens-algebra 범주의 초기 객체
    (universal property 의 유일성 절반).

    `hsym` 필요 이유: Raw 의 내부 canonicalisation (Tree.cmp)
    때문에 `L.view (slash x y h)` 는 canonical ordering 에 따라
    `combine (view x) (view y)` 또는 `combine (view y) (view x)`.
    둘이 같으려면 combine 대칭.  note 25 §3 의 Lens-layer
    observation.  -/
theorem Lens.view_unique {α : Type} (L : Lens α)
    (hsym : ∀ u v : α, L.combine u v = L.combine v u)
    (f : Raw → α)
    (ha : f Raw.a = L.base_a)
    (hb : f Raw.b = L.base_b)
    (hslash : ∀ (x y : Raw) (h : x ≠ y),
              f (Raw.slash x y h) = L.combine (f x) (f y)) :
    ∀ r : Raw, f r = L.view r := by
  intro r
  induction r using Raw.rec with
  | a => rw [ha]; rfl
  | b => rw [hb]; rfl
  | slash x y h ihx ihy =>
      rw [hslash x y h, ihx, ihy]
      -- Goal: L.combine (L.view x) (L.view y) = L.view (Raw.slash x y h).
      -- Raw.fold_slash 로 해결.
      symm
      show L.view (Raw.slash x y h) = L.combine (L.view x) (L.view y)
      exact Raw.fold_slash L.base_a L.base_b L.combine hsym x y h

end E213.Research.RawInitiality

namespace E213.Research.RawInitiality

open E213.Firmware E213.Hypervisor

/-! ## §2. 존재성 + 유일성 = universal property

존재성: `Lens.view L` 자체가 요구되는 homomorphism.
유일성: `Lens.view_unique` (§1).

### §2.1 존재성 witnesses (이미 Firmware 에 있음)
-/

/-- `L.view` 는 Raw.a 를 base_a 로 보낸다. -/
theorem Lens.view_a {α : Type} (L : Lens α) : L.view Raw.a = L.base_a := rfl

/-- `L.view` 는 Raw.b 를 base_b 로 보낸다. -/
theorem Lens.view_b {α : Type} (L : Lens α) : L.view Raw.b = L.base_b := rfl

/-- `L.view` 는 slash 를 combine 으로 보낸다 (commutative combine 하). -/
theorem Lens.view_slash {α : Type} (L : Lens α)
    (hsym : ∀ u v : α, L.combine u v = L.combine v u)
    (x y : Raw) (h : x ≠ y) :
    L.view (Raw.slash x y h) = L.combine (L.view x) (L.view y) :=
  Raw.fold_slash L.base_a L.base_b L.combine hsym x y h

/-! ### §2.2 Universal property corollary

존재성과 유일성 결합: 주어진 Lens 에 대한 homomorphism 은
정확히 하나.
-/

/-- **Universal property — 존재성 + 유일성 (commutative 조건부)**.
    Raw 는 commutative Raw-algebra 범주의 초기 객체.
    주어진 L 에 대해, L-호환 함수는 정확히 `L.view`. -/
theorem Lens.initiality {α : Type} (L : Lens α)
    (hsym : ∀ u v : α, L.combine u v = L.combine v u) :
    ∃ f : Raw → α,
      (f Raw.a = L.base_a) ∧
      (f Raw.b = L.base_b) ∧
      (∀ (x y : Raw) (h : x ≠ y),
        f (Raw.slash x y h) = L.combine (f x) (f y)) ∧
      (∀ g : Raw → α,
        g Raw.a = L.base_a →
        g Raw.b = L.base_b →
        (∀ x y h, g (Raw.slash x y h) = L.combine (g x) (g y)) →
        g = f) := by
  refine ⟨L.view, ?_, ?_, ?_, ?_⟩
  · exact Lens.view_a L
  · exact Lens.view_b L
  · intro x y h; exact Lens.view_slash L hsym x y h
  · intro g ha hb hslash
    funext r
    exact Lens.view_unique L hsym g ha hb hslash r

end E213.Research.RawInitiality
