/-
  E213/Theorem/Swap.lean — swap(e₂↔e₃) 보존

  e₂와 e₃는 공리 체계에서 구별 불가능.
  고유 공리는 3개뿐 (전부 e₁에 관한 것).
-/
import E213.Axiom

open Expr

theorem E.swap_swap (e : E) : e.swap.swap = e := by
  cases e <;> rfl

theorem Expr.swap_swap (e : Expr) : e.swap.swap = e := by
  induction e with
  | atom e => simp [Expr.swap, E.swap_swap]
  | plus a b iha ihb => simp [Expr.swap, iha, ihb]
  | times a b iha ihb => simp [Expr.swap, iha, ihb]

theorem swap_preserves_equiv {a b : Expr}
    (h : a ≈ b) : a.swap ≈ b.swap := by
  induction h with
  | refl a => exact Equiv.refl a.swap
  | symm _ ih => exact Equiv.symm ih
  | trans _ _ ih1 ih2 => exact Equiv.trans ih1 ih2
  | plus_comm a b => exact Equiv.plus_comm a.swap b.swap
  | times_comm a b => exact Equiv.times_comm a.swap b.swap
  | plus_assoc a b c =>
    exact Equiv.plus_assoc a.swap b.swap c.swap
  | times_assoc a b c =>
    exact Equiv.times_assoc a.swap b.swap c.swap
  | plus_e1 a =>
    show plus (atom (E.swap .e1)) a.swap ≈ a.swap
    simp [E.swap]; exact Equiv.plus_e1 a.swap
  | times_e1 a =>
    show times (atom (E.swap .e1)) a.swap ≈ atom (E.swap .e1)
    simp [E.swap]; exact Equiv.times_e1 a.swap
  | plus_cong _ _ ih1 ih2 => exact Equiv.plus_cong ih1 ih2
  | times_cong _ _ ih1 ih2 => exact Equiv.times_cong ih1 ih2
  | distrib a b c =>
    exact Equiv.distrib a.swap b.swap c.swap
