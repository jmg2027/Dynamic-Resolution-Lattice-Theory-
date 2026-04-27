import E213.Physics.SimplexCounts

/-!
# Phase 4 — AtomicExpr framework

★ User insight ★ "decide-check only is number games.  Real
formalization is needed."

## Idea

The *true* meaning of an atomic integer = not a simple arithmetic match
→ expressible as a short atomic expression.

  AtomicExpr : syntax = const(NS, NT, d) + (+, ·, -, ^).
  complexity : *operation count* of expression (description length).
  eval : expression → Nat.

Physical integers being derivable as atomic expressions of *small complexity*
= non-trivial claim.

  vs random integer N: average complexity ~ log N.
  Physical integers: complexity ≤ K (small constant).

## This file

  - AtomicExpr syntax definition
  - complexity definition
  - eval definition
  - atomic representation existence for key integers
-/

namespace E213.Physics.Phase4.AtomicExpr

open E213.Physics.Simplex

/-- Atomic expression syntax.  Only *(NS, NT, d)* primitives are const. -/
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
