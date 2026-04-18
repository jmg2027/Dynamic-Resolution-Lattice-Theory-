import E213.Firmware.Reachable

/-
  Hypervisor Layer: Equivalence (≡).

  Firmware에는 / 와 ≠ 만. = 는 없음.
  Hypervisor가 관계 ≡ 를 도입.

  정의: x ≡ y ↔ 두 Raw 트리가 구조적으로 같음.
  (Lean의 DecidableEq Raw를 끌어올림.)

  증명:
    1. ≡는 동치관계 (refl, symm, trans).
    2. slash가 ≡를 보존 (congruence).
    3. ≡는 판정 가능.
    4. ≡는 ≠의 부정과 일치 (firmware와 비순환 연결).
-/

-- ≡: 213에서 "같다"는 관계. Firmware에 없었음.
def Raw.equiv (x y : Raw) : Prop := x = y

-- ≡ 표기.
infix:50 " ≡ " => Raw.equiv

-- ═══ 1. 동치관계 ═══

theorem equiv_refl (x : Raw) : x ≡ x := rfl

theorem equiv_symm {x y : Raw} (h : x ≡ y) : y ≡ x := h.symm

theorem equiv_trans {x y z : Raw} (h1 : x ≡ y) (h2 : y ≡ z) : x ≡ z :=
  h1.trans h2

-- ═══ 2. slash가 ≡를 보존 (congruence) ═══

theorem equiv_slash {x x' y y' : Raw}
    (hx : x ≡ x') (hy : y ≡ y')
    (h : x ≠ y) (h' : x' ≠ y') :
    slash x y h ≡ slash x' y' h' := by
  simp [Raw.equiv, slash]
  exact ⟨hx, hy⟩

-- ═══ 3. ≡는 판정 가능 ═══

instance : DecidableEq Raw := inferInstance

instance (x y : Raw) : Decidable (x ≡ y) := inferInstanceAs (Decidable (x = y))

-- ═══ 4. ≡와 ≠의 비순환 연결 ═══

-- 두 Raw가 ≡가 아니면 ≠ (firmware 전제조건).
theorem not_equiv_iff_ne (x y : Raw) : ¬(x ≡ y) ↔ x ≠ y := by
  simp [Raw.equiv]

-- 그래서 slash의 전제조건은 정확히 "¬ equiv":
theorem slash_requires_not_equiv (x y : Raw) :
    (∃ h : x ≠ y, slash x y h = slash x y h) ↔ ¬(x ≡ y) := by
  rw [not_equiv_iff_ne]
  constructor
  · rintro ⟨h, _⟩; exact h
  · intro h; exact ⟨h, rfl⟩
