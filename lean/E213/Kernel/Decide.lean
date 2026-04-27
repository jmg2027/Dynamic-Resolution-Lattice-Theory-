import E213.Kernel.Term

/-!
# E213.Kernel.Decide — finite-enumeration decision procedures.

Lean 의 `decide` tactic 은 `Decidable` typeclass + Classical 영역 을
종종 끌어옴.  유한 이산 격자 에선 *순수 Bool 함수 + 유한 재귀* 면
충분 → typeclass 우회.

  allBelow n p   = ∀ x < n, p x = true   (Bool)
  existsBelow n p = ∃ x < n, p x = true  (Bool)

전부 구조귀납 + Bool 연산 → 0 axiom.
-/

namespace E213.Kernel.Decide

/-- ∀ x < n, p x 의 Bool 버전. -/
def allBelow : Nat → (Nat → Bool) → Bool
  | 0,     _ => true
  | n+1,   p => (allBelow n p) && p n

/-- ∃ x < n, p x 의 Bool 버전. -/
def existsBelow : Nat → (Nat → Bool) → Bool
  | 0,     _ => false
  | n+1,   p => (existsBelow n p) || p n

end E213.Kernel.Decide

namespace E213.Kernel.Decide.Tests

/-- d (= 5) 미만 의 모든 수가 ≤ 4. -/
theorem all_lt_d_le_4 :
    allBelow 5 (fun x => Nat.ble x 4) = true := rfl

/-- d 미만 에 4 가 존재. -/
theorem exists_lt_d_eq_4 :
    existsBelow 5 (fun x => Nat.beq x 4) = true := rfl

/-- d 미만 에 5 는 부재. -/
theorem no_lt_d_eq_5 :
    existsBelow 5 (fun x => Nat.beq x 5) = false := rfl

/-- 25 미만 의 모든 페어 (i, j) 에 대해 i + j ≤ 48.
    (가벼운 sanity 검사 — d² 격자 안 sum bound). -/
theorem pair_sum_bound :
    allBelow 25 (fun i =>
      allBelow 25 (fun j => Nat.ble (i + j) 48)) = true := rfl

/-- magic numbers (2, 8, 20, 28, 50, 82, 126) 모두 ≤ 126. -/
theorem magic_le_126 :
    [2, 8, 20, 28, 50, 82, 126].all (fun n => Nat.ble n 126) = true := rfl

/-- magic numbers 모두 짝수. -/
theorem magic_all_even :
    [2, 8, 20, 28, 50, 82, 126].all (fun n => Nat.beq (n % 2) 0) = true := rfl

end E213.Kernel.Decide.Tests

#print axioms E213.Kernel.Decide.Tests.all_lt_d_le_4
#print axioms E213.Kernel.Decide.Tests.exists_lt_d_eq_4
#print axioms E213.Kernel.Decide.Tests.no_lt_d_eq_5
#print axioms E213.Kernel.Decide.Tests.pair_sum_bound
#print axioms E213.Kernel.Decide.Tests.magic_le_126
#print axioms E213.Kernel.Decide.Tests.magic_all_even
