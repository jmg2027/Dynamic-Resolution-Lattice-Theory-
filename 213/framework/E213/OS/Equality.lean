import E213.OS.Peano

/-
  질문: Peano의 =은 213에서 어떻게 나오는가?

  답 (정직하게):
    - 213 Firmware 자체에는 = 없음. ≠ 만 (slash 전제).
    - Lean (Hardware) 이 = 제공 (DecidableEq Raw).
    - Hypervisor (Equiv.lean) 가 Raw.equiv := (· = ·) 로 명시 노출.
    - Peano (OS) 의 = 은 Nat213 구조적 =.
    - Nat213 의 = 은 toRaw 를 거쳐 Raw 의 ≡ 로 환원.

  환원 체인 (증명 대상):
    m = n  ↔  m.toRaw ≡ n.toRaw  ↔  ¬ (m.toRaw ≠ n.toRaw)
    (OS)      (Hypervisor)         (Firmware 전제의 부정)

  솔직한 의미:
    213만으로는 = 얘기 못함. Hardware 를 빌려야 함.
    이건 bootstrap (논리를 논리로 말하기).
    하지만 Firmware 는 순수하게 ≠ 로 작동.
-/

-- ═══ 환원 1: Nat213의 =  ↔  Raw의 ≡ ═══

theorem Nat213.eq_iff_toRaw_equiv (m n : Nat213) :
    m = n ↔ m.toRaw ≡ n.toRaw := by
  constructor
  · intro h; rw [h]
  · intro h; exact toRaw_inj h

-- ═══ 환원 2: Raw의 ≡  ↔  ¬ (Raw의 ≠) ═══

-- not_equiv_iff_ne 는 Equiv.lean 에 있음: ¬(x ≡ y) ↔ x ≠ y.
-- 대우: x ≡ y ↔ ¬ (x ≠ y).
theorem Raw.equiv_iff_not_ne (x y : Raw) : x ≡ y ↔ ¬ (x ≠ y) := by
  simp [Raw.equiv]

-- ═══ 합성: Nat213의 =  ↔  ¬ (Firmware의 ≠) ═══

theorem Nat213.eq_iff_not_toRaw_ne (m n : Nat213) :
    m = n ↔ ¬ (m.toRaw ≠ n.toRaw) := by
  rw [eq_iff_toRaw_equiv, Raw.equiv_iff_not_ne]

-- 완전한 환원: Peano 의 = 은 Firmware 의 ≠ 의 부정.
-- Firmware 는 ≠ 만 가지지만, 그 부정 (¬ ≠) 을 Hypervisor 가 ≡ 로 이름.
-- Peano 는 그 ≡ 를 Nat213 수준으로 끌어올림.

-- 결론: Peano 의 모든 = 사용은, / 의 전제조건 (≠) 을 부정한 것.
-- = 은 213 공리 밖에서 빌려오지만, 그 의미는 / 의 전제조건으로 환원.
