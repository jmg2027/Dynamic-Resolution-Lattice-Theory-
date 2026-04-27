import E213.Kernel.Term
import E213.Kernel.Compare

/-!
# E213.Kernel.Sound — bridge between deep ↔ shallow embedding.

`equiv a b = true` (Bool, deep) → `eval a = eval b` (Lean Eq, shallow).
`Nat.eq_of_beq_eq_true` uses only structural induction, no propext dependency →
this bridge also has 0 axioms.

The Sound bridge is needed to *upgrade* deep capstone results into
shallow Lean theorems — making them convenient to cite externally.
-/

namespace E213.Kernel.Sound

open Term

/-- equiv = true → eval equality. -/
theorem of_equiv {a b : Term} (h : equiv a b = true) : eval a = eval b :=
  Nat.eq_of_beq_eq_true h

/-- le_b = true → eval ≤ (less-or-equal). -/
theorem of_le_b {a b : Term} (h : le_b a b = true) : eval a ≤ eval b :=
  Nat.le_of_ble_eq_true h

/-- propext-free version of beq reflexivity (structural induction). -/
private theorem beq_refl' : ∀ (n : Nat), Nat.beq n n = true
  | 0     => rfl
  | n+1   => beq_refl' n

/-- Converse: eval equality → equiv = true.  Eq.subst + internal beq_refl. -/
theorem to_equiv {a b : Term} (h : eval a = eval b) : equiv a b = true :=
  @Eq.subst Nat (fun x => Nat.beq (eval a) x = true)
    (eval a) (eval b) h (beq_refl' (eval a))

/-- Application: promotes dim_law from Demo into Lean Eq form. -/
theorem dim_law_eq : eval (add nS nT) = eval d :=
  of_equiv rfl

/-- Application: d² = 25 (Lean Eq). -/
theorem d_sq_eq_25 : eval (mul d d) = 25 := rfl

/-- Application: 2 n_S² < d² (strict, Lean Lt). -/
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
