import E213.Kernel.Term
import E213.Kernel.Compare

/-!
# E213.Kernel.Sound — deep ↔ shallow embedding 다리.

`equiv a b = true` (Bool, deep) → `eval a = eval b` (Lean Eq, shallow).
`Nat.eq_of_beq_eq_true` 가 구조귀납만 사용하므로 propext 미의존 →
이 다리도 0 axiom.

Sound 다리가 있어야 deep capstone 결과가 shallow Lean 정리로
*upgrade* 됨 — 외부에서 인용하기 편해짐.
-/

namespace E213.Kernel.Sound

open Term

/-- equiv = true → eval 동등. -/
theorem of_equiv {a b : Term} (h : equiv a b = true) : eval a = eval b :=
  Nat.eq_of_beq_eq_true h

/-- le_b = true → eval ≤. -/
theorem of_le_b {a b : Term} (h : le_b a b = true) : eval a ≤ eval b :=
  Nat.le_of_ble_eq_true h

/-- propext-free 버전 의 beq reflexivity (구조귀납). -/
private theorem beq_refl' : ∀ (n : Nat), Nat.beq n n = true
  | 0     => rfl
  | n+1   => beq_refl' n

/-- 역: eval 동등 → equiv = true.  Eq.subst + 자체 beq_refl. -/
theorem to_equiv {a b : Term} (h : eval a = eval b) : equiv a b = true :=
  @Eq.subst Nat (fun x => Nat.beq (eval a) x = true)
    (eval a) (eval b) h (beq_refl' (eval a))

/-- 응용: Demo 의 dim_law 를 Lean Eq 형태로 승격. -/
theorem dim_law_eq : eval (add nS nT) = eval d :=
  of_equiv rfl

/-- 응용: d² = 25 (Lean Eq). -/
theorem d_sq_eq_25 : eval (mul d d) = 25 := rfl

/-- 응용: 2 n_S² < d² (strict, Lean Lt). -/
theorem two_nSsq_lt_dsq :
    eval (mul (succ (succ zero)) (mul nS nS)) < eval (mul d d) :=
  Nat.lt_of_lt_of_le (by decide : 18 < 25) (Nat.le_refl 25)

end E213.Kernel.Sound

#print axioms E213.Kernel.Sound.of_equiv
#print axioms E213.Kernel.Sound.of_le_b
#print axioms E213.Kernel.Sound.to_equiv
#print axioms E213.Kernel.Sound.dim_law_eq
#print axioms E213.Kernel.Sound.d_sq_eq_25
#print axioms E213.Kernel.Sound.two_nSsq_lt_dsq
