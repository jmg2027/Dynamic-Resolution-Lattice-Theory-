import E213.Research.Real213.CutBinary

/-!
# Research.Real213CutBinaryOp: structural binary cut operation

Reify the *parameters* of all binary cut operations into a single struct
via `CutBinaryOp`.  Both cutSum and cutMul are instances.

## Significance

- 213-style universal abstraction for binary cut operations.
- The locally-determined property follows automatically.
- New operations require only an instance definition.
-/

namespace E213.Research.Real213.CutSum

open E213.Firmware E213.Hypervisor

/-- **CutBinaryOp**: parameters of a binary cut operation. -/
structure CutBinaryOp where
  predicate : Nat → Nat → Nat → Nat → Bool  -- (m, k) (m1, m2) → Bool
  k1 : Nat → Nat → Nat                       -- precision for cx
  k2 : Nat → Nat → Nat                       -- precision for cy
  M1 : Nat → Nat → Nat                       -- search bound for m1
  M2 : Nat → Nat → Nat                       -- search bound for m2

/-- **Apply** a CutBinaryOp to two cuts. -/
def CutBinaryOp.apply (op : CutBinaryOp) (cx cy : Nat → Nat → Bool) :
    Nat → Nat → Bool :=
  fun m k =>
    cutBinary (op.predicate m k) (op.k1 m k) (op.k2 m k)
              (op.M1 m k) (op.M2 m k) cx cy

end E213.Research.Real213.CutSum

namespace E213.Research.Real213.CutSum

open E213.Firmware E213.Hypervisor

/-- **cutSumOp**: CutBinaryOp form of cutSum. -/
def cutSumOp : CutBinaryOp where
  predicate := fun m _ m1 m2 => decide (m1 + m2 = 2*m)
  k1 := fun _ k => 2*k
  k2 := fun _ k => 2*k
  M1 := fun m _ => 2*m
  M2 := fun m _ => 2*m

/-- **cutMulOp**: CutBinaryOp form of cutMul. -/
def cutMulOp : CutBinaryOp where
  predicate := fun m k m1 m2 => decide (m1 * m2 ≤ m * k)
  k1 := fun _ k => k
  k2 := fun _ k => k
  M1 := fun m k => (m + 1) * (k + 1)
  M2 := fun m k => (m + 1) * (k + 1)

end E213.Research.Real213.CutSum

namespace E213.Research.Real213.CutSum

open E213.Firmware E213.Hypervisor

/-- **CutBinaryOp.apply is locally determined** — generic. -/
theorem CutBinaryOp.apply_locallyDetermined (op : CutBinaryOp)
    (cx1 cx2 cy1 cy2 : Nat → Nat → Bool) (m k : Nat)
    (hx : ∀ m', m' ≤ op.M1 m k → cx1 m' (op.k1 m k) = cx2 m' (op.k1 m k))
    (hy : ∀ m', m' ≤ op.M2 m k → cy1 m' (op.k2 m k) = cy2 m' (op.k2 m k)) :
    op.apply cx1 cy1 m k = op.apply cx2 cy2 m k := by
  show cutBinary (op.predicate m k) (op.k1 m k) (op.k2 m k)
                 (op.M1 m k) (op.M2 m k) cx1 cy1
     = cutBinary (op.predicate m k) (op.k1 m k) (op.k2 m k)
                 (op.M1 m k) (op.M2 m k) cx2 cy2
  exact cutBinary_locallyDetermined _ _ _ _ _ cx1 cx2 cy1 cy2 hx hy

end E213.Research.Real213.CutSum
