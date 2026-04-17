/-
  E213/Normalize.lean — 정규형 + 판정

  Expr → List Mon (정렬된 단항식) → BEq 비교.
  교환/결합/분배가 정규화에서 자동.
-/
import E213.Core

structure Mon where
  p : Nat    -- e₂ 차수
  q : Nat    -- e₃ 차수
  deriving Repr, BEq, DecidableEq

instance : Ord Mon where
  compare a b :=
    match compare a.p b.p with
    | .eq => compare a.q b.q
    | r => r

def Mon.mul (a b : Mon) : Mon := ⟨a.p + b.p, a.q + b.q⟩

def sortMon (l : List Mon) : List Mon :=
  l.mergeSort (compare · · |>.isLE)

def normalize : Expr → List Mon
  | .atom .e1 => []
  | .atom .e2 => [⟨1, 0⟩]
  | .atom .e3 => [⟨0, 1⟩]
  | .plus a b => sortMon (normalize a ++ normalize b)
  | .times a b =>
    sortMon ((normalize a).flatMap fun m1 =>
             (normalize b).map fun m2 => m1.mul m2)

def equivDecide (a b : Expr) : Bool :=
  normalize a == normalize b

-- eval: 관찰용 [매체]
def Mon.eval (m : Mon) (vx vy : Nat) : Nat :=
  vx ^ m.p * vy ^ m.q

def polyEval (p : List Mon) (vx vy : Nat) : Nat :=
  p.foldl (fun acc m => acc + m.eval vx vy) 0

def exprEval (e : Expr) (vx vy : Nat) : Nat :=
  polyEval (normalize e) vx vy
