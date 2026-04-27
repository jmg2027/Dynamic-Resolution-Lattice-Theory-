import E213.Physics.SimplexCounts

/-!
# Phase 4 — AtomicExpr framework

★ User insight ★ "decide-check 만 하는 건 number games.  진짜
formalization 필요."

## Idea

Atomic 정수 의 *진짜* 의미 = 단순 산수 매치 X → 짧은 atomic
expression 으로 표현 가능.

  AtomicExpr : 문법 = const(NS, NT, d) + (+, ·, -, ^).
  complexity : 표현 의 *operation 수* (description length).
  eval : 표현 → Nat.

물리 정수가 *작은 complexity* 의 atomic expression 으로 도출
가능 = non-trivial 주장.

  vs 무작위 정수 N: 평균 complexity ~ log N.
  물리 정수: complexity ≤ K (작은 상수).

## 본 파일

  - AtomicExpr 문법 정의
  - complexity 정의
  - eval 정의
  - 핵심 정수에 대해 atomic representation existence
-/

namespace E213.Physics.Phase4.AtomicExpr

open E213.Physics.Simplex

/-- Atomic expression syntax.  *(NS, NT, d)* primitive 만 const. -/
inductive Expr : Type
  | NSc  : Expr
  | NTc  : Expr
  | dc   : Expr
  | add  : Expr → Expr → Expr
  | mul  : Expr → Expr → Expr
  | sub  : Expr → Expr → Expr
  | pow  : Expr → Nat → Expr
  deriving Repr

/-- Evaluation: Expr → Nat (using NS=3, NT=2, d=5). -/
def eval : Expr → Nat
  | .NSc => NS
  | .NTc => NT
  | .dc  => d
  | .add a b => eval a + eval b
  | .mul a b => eval a * eval b
  | .sub a b => eval a - eval b
  | .pow a n => (eval a) ^ n

/-- Complexity = operation count (size of expr). -/
def complexity : Expr → Nat
  | .NSc => 0
  | .NTc => 0
  | .dc  => 0
  | .add a b => 1 + complexity a + complexity b
  | .mul a b => 1 + complexity a + complexity b
  | .sub a b => 1 + complexity a + complexity b
  | .pow a _ => 1 + complexity a

end E213.Physics.Phase4.AtomicExpr
