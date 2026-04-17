/-
  E213/Axiom.lean — 213의 12공리 (223)

  매체 비용 9 + 고유 3 = 12 = 2²×3.
-/
import E213.Core

open Expr

inductive Equiv : Expr → Expr → Prop where
  | refl (a : Expr) : Equiv a a
  | symm {a b} : Equiv a b → Equiv b a
  | trans {a b c} : Equiv a b → Equiv b c → Equiv a c
  | plus_comm (a b) : Equiv (plus a b) (plus b a)
  | times_comm (a b) : Equiv (times a b) (times b a)
  | plus_assoc (a b c) :
      Equiv (plus (plus a b) c) (plus a (plus b c))
  | times_assoc (a b c) :
      Equiv (times (times a b) c) (times a (times b c))
  | plus_e1 (a) : Equiv (plus (atom .e1) a) a
  | times_e1 (a) : Equiv (times (atom .e1) a) (atom .e1)
  | plus_cong {a a' b b'} :
      Equiv a a' → Equiv b b' → Equiv (plus a b) (plus a' b')
  | times_cong {a a' b b'} :
      Equiv a a' → Equiv b b' → Equiv (times a b) (times a' b')
  | distrib (a b c) :
      Equiv (times a (plus b c)) (plus (times a b) (times a c))

infix:50 " ≈ " => Equiv

-- 기본 따름정리
theorem boundary_plus (x : Expr) : plus e₁ x ≈ x :=
  Equiv.plus_e1 x

theorem boundary_times (x : Expr) : times e₁ x ≈ e₁ :=
  Equiv.times_e1 x

theorem plus_boundary (x : Expr) : plus x e₁ ≈ x :=
  Equiv.trans (Equiv.plus_comm x e₁) (Equiv.plus_e1 x)

theorem zero_is_boundary : plus e₁ e₁ ≈ e₁ :=
  Equiv.plus_e1 e₁
