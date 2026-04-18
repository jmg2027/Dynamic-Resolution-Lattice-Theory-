-- 213 Phase 9: swap 대칭 + 3공리 환원
--
-- e₂와 e₃를 교환해도 모든 Equiv가 보존됨을 증명.
-- 함의: comm, assoc는 매체 비용. 213 고유 공리는 3개뿐.

inductive E where
  | e1 : E | e2 : E | e3 : E
  deriving Repr, BEq, DecidableEq

open E

inductive Expr where
  | atom : E → Expr
  | plus : Expr → Expr → Expr
  | times : Expr → Expr → Expr
  deriving Repr, BEq

open Expr

-- ═══ swap: e₂ ↔ e₃, e₁ 불변 ═══
def E.swap : E → E
  | e1 => e1
  | e2 => e3
  | e3 => e2

def Expr.swap : Expr → Expr
  | atom e => atom e.swap
  | plus a b => plus a.swap b.swap
  | times a b => times a.swap b.swap

-- ═══ 12공리 (223 체계) ═══
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
  | plus_e1 (a) : Equiv (plus (atom e1) a) a
  | times_e1 (a) : Equiv (times (atom e1) a) (atom e1)
  | plus_cong {a a' b b'} :
      Equiv a a' → Equiv b b' → Equiv (plus a b) (plus a' b')
  | times_cong {a a' b b'} :
      Equiv a a' → Equiv b b' → Equiv (times a b) (times a' b')
  | distrib (a b c) :
      Equiv (times a (plus b c)) (plus (times a b) (times a c))

infix:50 " ≈ " => Equiv

-- ═══ swap이 Equiv를 보존함 ═══
-- 핵심 정리: a ≈ b → a.swap ≈ b.swap

-- 보조: e₁.swap = e₁
theorem e1_swap_fixed : E.swap e1 = e1 := rfl

-- 보조: swap은 involution (두 번 하면 원래)
theorem E.swap_swap (e : E) : e.swap.swap = e := by
  cases e <;> rfl

theorem Expr.swap_swap (e : Expr) : e.swap.swap = e := by
  induction e with
  | atom e => simp [Expr.swap, E.swap_swap]
  | plus a b iha ihb => simp [Expr.swap, iha, ihb]
  | times a b iha ihb => simp [Expr.swap, iha, ihb]

-- ★ 핵심 정리: swap이 Equiv를 보존한다 ★
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
    show plus (atom (E.swap e1)) a.swap ≈ a.swap
    simp [E.swap]
    exact Equiv.plus_e1 a.swap
  | times_e1 a =>
    show times (atom (E.swap e1)) a.swap ≈ atom (E.swap e1)
    simp [E.swap]
    exact Equiv.times_e1 a.swap
  | plus_cong _ _ ih1 ih2 => exact Equiv.plus_cong ih1 ih2
  | times_cong _ _ ih1 ih2 => exact Equiv.times_cong ih1 ih2
  | distrib a b c =>
    exact Equiv.distrib a.swap b.swap c.swap

-- ═══ 함의 ═══
-- swap이 Equiv를 보존한다는 것은:
-- e₂와 e₃가 공리 체계에서 구별되지 않는다는 뜻.
-- 12 공리 중 어느 것도 e₂와 e₃를 비대칭으로 취급하지 않음.
-- 구조는 {e₁(경계), e₂(내용), e₃(내용)}이지
-- {e₁(경계), e₂(구분), e₃(창발)}이 아님.

-- ═══ 3공리 환원 ═══
-- comm, assoc는 "순서가 있어서 필요한 보정" = 매체 비용
-- refl, symm, trans는 동치관계 인프라 = 매체 비용
-- cong는 합동 전파 = 매체 비용
-- 213 고유 공리 = plus_e1, times_e1, distrib = 3개

-- 이 3개의 공통점: 전부 e₁(경계)에 관한 것.
-- plus_e1:  경계 + X = X (경계는 +에 투명)
-- times_e1: 경계 × X = 경계 (경계는 ×에 소멸)
-- distrib:  ×가 +를 관통 (연산의 연결)
