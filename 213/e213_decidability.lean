-- 213: Equiv 결정가능성
import Mathlib.Tactic.Basic
import Mathlib.Data.List.Sort

inductive E where | e1 | e2 | e3
  deriving Repr, BEq, DecidableEq
open E

inductive Expr where
  | atom : E → Expr
  | plus : Expr → Expr → Expr
  | times : Expr → Expr → Expr
  deriving Repr, BEq
open Expr

structure Term where
  p : Nat
  q : Nat
  deriving Repr, BEq, DecidableEq

instance : Ord Term where
  compare a b :=
    match compare a.p b.p with
    | .eq => compare a.q b.q
    | r => r

def Term.mul (a b : Term) : Term := ⟨a.p + b.p, a.q + b.q⟩

def sortT (l : List Term) : List Term :=
  l.mergeSort (fun a b => (compare a b).isLE)

def normalize : Expr → List Term
  | atom e1 => []
  | atom e2 => [⟨1, 0⟩]
  | atom e3 => [⟨0, 1⟩]
  | plus a b => sortT (normalize a ++ normalize b)
  | times a b =>
    sortT ((normalize a).flatMap fun t1 =>
           (normalize b).map fun t2 => t1.mul t2)

def equivDecide (a b : Expr) : Bool := normalize a == normalize b

def e₁ := atom e1
def e₂ := atom e2
def e₃ := atom e3

#eval equivDecide (plus e₂ e₃) (plus e₃ e₂)           -- true
#eval equivDecide (plus (plus e₂ e₃) e₂)
                  (plus e₂ (plus e₃ e₂))              -- true
#eval equivDecide (times e₂ (plus e₃ e₂))
  (plus (times e₂ e₃) (times e₂ e₂))                 -- true
#eval equivDecide (plus e₁ e₃) e₃                     -- true
#eval equivDecide (times e₁ e₃) e₁                    -- true
#eval equivDecide e₂ e₃                               -- false
#eval equivDecide (plus e₂ e₃) (times e₂ e₃)          -- false
-- Equiv는 결정가능. 정규형으로 환원.
