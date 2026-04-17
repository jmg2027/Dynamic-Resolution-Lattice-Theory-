/-
  E213/Core.lean — 213의 유일한 정의 출처

  E, Expr, 편의 표기.
  이 파일을 고치면 전체가 바뀐다.
  이 파일 외에서 E나 Expr을 재정의하지 않는다.
-/
import Init

inductive E where
  | e1 : E
  | e2 : E
  | e3 : E
  deriving Repr, BEq, DecidableEq

open E

inductive Expr where
  | atom : E → Expr
  | plus : Expr → Expr → Expr
  | times : Expr → Expr → Expr
  deriving Repr, BEq

open Expr

-- 편의
def e₁ : Expr := atom e1
def e₂ : Expr := atom e2
def e₃ : Expr := atom e3

-- swap: e₂ ↔ e₃
def E.swap : E → E
  | e1 => e1 | e2 => e3 | e3 => e2

def Expr.swap : Expr → Expr
  | atom e => atom e.swap
  | plus a b => plus a.swap b.swap
  | times a b => times a.swap b.swap
