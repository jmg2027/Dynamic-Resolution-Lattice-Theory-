import E213.Applications.StreamAnalysis

/-
  수론 정리: Fermat little, Wilson (Z3 기반).

  Z3 에서 p=3 소수 판정 가능.
  Fermat: a^p = a (mod p). Z3: a^3 = a.
  Wilson: (p-1)! ≡ -1 (mod p). Z3: 2! = 2 = -1 mod 3.

  Z3 곱셈 정의 추가 (기존 Fin3.add 외).
-/

-- ═══ Z3 곱셈 ═══

def Fin3.mul : Fin 3 → Fin 3 → Fin 3 :=
  fun a b => ⟨(a.val * b.val) % 3, Nat.mod_lt _ (by decide)⟩

-- 확인.
example : Fin3.mul ⟨1, by decide⟩ ⟨2, by decide⟩ = ⟨2, by decide⟩ := by decide
example : Fin3.mul ⟨2, by decide⟩ ⟨2, by decide⟩ = ⟨1, by decide⟩ := by decide

-- ═══ Fermat's Little Theorem: a^3 = a (mod 3) ═══

-- a^3 := (a * a) * a.
theorem fermat_little_Z3 (a : Fin 3) :
    Fin3.mul (Fin3.mul a a) a = a := by
  revert a; decide

-- 의미: Z3 에서 모든 원소가 3 거듭제곱 고정점.

-- ═══ Wilson's Theorem: 2! = -1 (mod 3) ═══

-- 2! = 1 * 2 = 2.
-- -1 mod 3 = 2.
-- 따라서 2! ≡ -1 (mod 3). ✓

theorem wilson_Z3 :
    Fin3.mul ⟨1, by decide⟩ ⟨2, by decide⟩ =
    ⟨(3 - 1) % 3, by decide⟩ := by decide

-- ═══ Z3 은 필드 (field) ═══

-- 모든 비-0 원소 역원 존재 (mul).
theorem Z3_inverse_exists :
    ∀ a : Fin 3, a ≠ ⟨0, by decide⟩ → ∃ b, Fin3.mul a b = ⟨1, by decide⟩ := by
  intro a ha
  revert a ha
  decide

-- ═══ Distributive ═══

theorem Z3_distributive (a b c : Fin 3) :
    Fin3.mul a (Fin3.add b c) =
    Fin3.add (Fin3.mul a b) (Fin3.mul a c) := by
  revert a b c; decide
