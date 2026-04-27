import E213.Research.Real213CutBisection
import E213.Research.Real213CutPoset

/-!
# Research.Real213CutBisectionAlgo: bisection iteration + IVT scaffold

## Algorithm

```
bisect a b oracle n :
  if n = 0: (a, b)
  else:
    m := mid(a, b)
    if oracle(m): bisect a m oracle (n-1)  -- root in [a, m]
    else:         bisect m b oracle (n-1)  -- root in [m, b]
```

After n iterations, bracket length ≤ (b - a) / 2^n.

## 의의

IVT 의 algorithmic 형식 — given continuous f and bracket [a, b]
with sign change, iterative midpoint refinement.  Output: bracket
sequence converging to root.
-/

namespace E213.Research.Real213CutSum

open E213.Firmware E213.Hypervisor

/-- **Sign oracle**: cut-level "is f(x) ≤ 0 at given query"? -/
abbrev SignOracle := (Nat → Nat → Bool) → Nat → Nat → Bool

/-- **Bisection step**: one iteration. -/
def bisectStep (a b : Nat → Nat → Bool) (oracle : Nat → Nat → Bool → Bool)
    (m k : Nat) : (Nat → Nat → Bool) × (Nat → Nat → Bool) :=
  let mid := cutMid a b
  if oracle m k (mid m k) then (a, mid) else (mid, b)

/-- **Bisection iteration**: n steps. -/
def bisectN (a b : Nat → Nat → Bool) (oracle : Nat → Nat → Bool → Bool) :
    Nat → Nat → Nat → (Nat → Nat → Bool) × (Nat → Nat → Bool)
  | 0, _, _ => (a, b)
  | n+1, m, k =>
    let mid := cutMid a b
    if oracle m k (mid m k) then bisectN a mid oracle n m k
    else bisectN mid b oracle n m k

end E213.Research.Real213CutSum

namespace E213.Research.Real213CutSum

open E213.Firmware E213.Hypervisor

/-- **Bracket sequence at fixed (m, k)**: from bisectN, extract n-th
    bracket midpoint cut value. -/
def bisectMidValue (a b : Nat → Nat → Bool) (oracle : Nat → Nat → Bool → Bool)
    (n m k : Nat) : Bool :=
  let p := bisectN a b oracle n m k
  cutMid p.1 p.2 m k

end E213.Research.Real213CutSum
