import E213.Meta.Tactic.Nat213
import E213.Lib.Math.Real213.Sum.CutSum
import E213.Lib.Math.Real213.Sum.CutSumTest
import E213.Lib.Math.Real213.Sum.CutSumOne
import E213.Lib.Math.Real213.Bisection.CutBisection
import E213.Lib.Math.Real213.Core.Core.CutPoset

import E213.Lib.Math.Real213.Mul.CutMul
/-!
# CutDouble: 2x cut function

cutDouble c := "2x ≤ m/k" iff "x ≤ m/(2k)" → c m (2k).
-/

namespace E213.Lib.Math.Real213.Mul.CutDouble

open E213.Lib.Math.Real213.Sum.CutSum (cutSum cutSumAux)
open E213.Lib.Math.Real213.Sum.CutSumTest (constCut)
open E213.Lib.Math.Real213.Sum.CutSumOne (cutSum_self cutSum_self_at)
open E213.Lib.Math.Real213.Bisection.CutBisection (cutHalf cutHalf_constCut cutMid)
open E213.Lib.Math.Real213.Mul.CutMul (cutMul)
open E213.Lib.Math.Real213.Core.Core.CutPoset (cutEq cutLe)
open E213.Theory E213.Lens

/-- **cutDouble**: 2x cut. -/
def cutDouble (c : Nat → Nat → Bool) : Nat → Nat → Bool :=
  fun m k => c m (2*k)

/-- cutDouble of const = const pointwise (PURE). -/
theorem cutDouble_constCut_at (a b m k : Nat) :
    cutDouble (constCut a b) m k = constCut (2*a) b m k := by
  show decide (a * (2*k) ≤ b * m) = decide (2 * a * k ≤ b * m)
  rw [← E213.Tactic.Nat213.mul_assoc, Nat.mul_comm a 2]

/-- cutDouble of const ≡ const with doubled numerator (cutEq, PURE). -/
theorem cutDouble_constCut (a b : Nat) :
    cutEq (cutDouble (constCut a b)) (constCut (2*a) b) :=
  cutDouble_constCut_at a b

/-- 2 * (1/2) ≡ 1: cutDouble (1/2) cut-equivalent to constCut 2 2. -/
example : cutEq (cutDouble (constCut 1 2)) (constCut 2 2) := cutDouble_constCut 1 2

/-- cutDouble of zero pointwise (PURE). -/
theorem cutDouble_zero_at (m k : Nat) :
    cutDouble (constCut 0 1) m k = constCut 0 1 m k := by
  show constCut 0 1 m (2*k) = constCut 0 1 m k
  show decide (0 * (2*k) ≤ 1 * m) = decide (0 * k ≤ 1 * m)
  rw [Nat.zero_mul, Nat.zero_mul]

/-- cutDouble of zero ≡ zero (cutEq, PURE). -/
theorem cutDouble_zero : cutEq (cutDouble (constCut 0 1)) (constCut 0 1) :=
  cutDouble_zero_at

/-- cutDouble of cutDouble pointwise (PURE). -/
theorem cutDouble_cutDouble_at (c : Nat → Nat → Bool) (m k : Nat) :
    cutDouble (cutDouble c) m k = c m (4*k) := by
  show c m (2*(2*k)) = c m (4*k)
  congr 1
  rw [← E213.Tactic.Nat213.mul_assoc]

/-- cutDouble of cutDouble ≡ quadruple: c m (4k) (cutEq, PURE). -/
theorem cutDouble_cutDouble (c : Nat → Nat → Bool) :
    cutEq (cutDouble (cutDouble c)) (fun m k => c m (4*k)) :=
  cutDouble_cutDouble_at c

/-- **cutSum c c ≡ cutDouble c** for c = constCut a b (cutEq, PURE). -/
theorem cutSum_self_eq_cutDouble (a b : Nat) :
    cutEq (cutSum (constCut a b) (constCut a b)) (cutDouble (constCut a b)) := by
  intro m k
  rw [cutSum_self_at a b m k]
  exact (cutDouble_constCut_at a b m k).symm

/-- **cutDouble and cutHalf commute** universally (rfl, PURE). -/
theorem cutDouble_cutHalf_comm (c : Nat → Nat → Bool) :
    cutDouble (cutHalf c) = cutHalf (cutDouble c) := rfl

/-- **cutHalf (cutHalf (a/b)) ≡ a/(4b)** (cutEq, PURE). -/
theorem cutHalf_cutHalf_constCut (a b : Nat) :
    cutEq (cutHalf (cutHalf (constCut a b))) (constCut a (4*b)) := by
  intro m k
  show constCut a b (2*(2*m)) k = constCut a (4*b) m k
  show decide (a * k ≤ b * (2*(2*m))) = decide (a * k ≤ (4*b) * m)
  have e1 : (2:Nat)*(2*m) = 4*m := by
    rw [← E213.Tactic.Nat213.mul_assoc]
  have e2 : b * (4*m) = 4*b*m := by
    rw [← E213.Tactic.Nat213.mul_assoc, Nat.mul_comm b 4]
  rw [e1, e2]

/-- **cutDouble (cutDouble (a/b)) ≡ (4a)/b** (cutEq, PURE). -/
theorem cutDouble_cutDouble_constCut (a b : Nat) :
    cutEq (cutDouble (cutDouble (constCut a b))) (constCut (4*a) b) := by
  intro m k
  show constCut a b m (2*(2*k)) = constCut (4*a) b m k
  show decide (a * (2*(2*k)) ≤ b * m) = decide ((4*a) * k ≤ b * m)
  have e1 : (2:Nat)*(2*k) = 4*k := by
    rw [← E213.Tactic.Nat213.mul_assoc]
  have e2 : a * (4*k) = 4*a*k := by
    rw [← E213.Tactic.Nat213.mul_assoc, Nat.mul_comm a 4]
  rw [e1, e2]

/-- cutDouble preserves cutEq. -/
theorem cutDouble_cutEq (cx cy : Nat → Nat → Bool)
    (h : cutEq cx cy) : cutEq (cutDouble cx) (cutDouble cy) :=
  fun m k => h m (2*k)

/-- cutDouble preserves cutLe. -/
theorem cutDouble_cutLe (cx cy : Nat → Nat → Bool)
    (h : cutLe cx cy) : cutLe (cutDouble cx) (cutDouble cy) :=
  fun m k => h m (2*k)

/-- cutHalf preserves cutEq. -/
theorem cutHalf_cutEq (cx cy : Nat → Nat → Bool)
    (h : cutEq cx cy) : cutEq (cutHalf cx) (cutHalf cy) :=
  fun m k => h (2*m) k

/-- cutHalf preserves cutLe. -/
theorem cutHalf_cutLe (cx cy : Nat → Nat → Bool)
    (h : cutLe cx cy) : cutLe (cutHalf cx) (cutHalf cy) :=
  fun m k => h (2*m) k

/-- cutSumAux for doubled cuts at precision k = cutSumAux for original
    cuts at precision (2k) — doubling acts on the inner k slot. -/
theorem cutSumAux_cutDouble (cx cy : Nat → Nat → Bool)
    (k m1Max : Nat) :
    ∀ n, cutSumAux (cutDouble cx) (cutDouble cy) k m1Max n
       = cutSumAux cx cy (2*k) m1Max n
  | 0 => rfl
  | n+1 => by
    show ((cx (n+1) (2*(2*k)) && cy (m1Max - (n+1)) (2*(2*k)))
          || cutSumAux (cutDouble cx) (cutDouble cy) k m1Max n)
       = ((cx (n+1) (2*(2*k)) && cy (m1Max - (n+1)) (2*(2*k)))
          || cutSumAux cx cy (2*k) m1Max n)
    rw [cutSumAux_cutDouble cx cy k m1Max n]

/-- **cutDouble distributes over cutSum**, pointwise (PURE). -/
theorem cutDouble_cutSum_at (cx cy : Nat → Nat → Bool) (m k : Nat) :
    cutDouble (cutSum cx cy) m k
    = cutSum (cutDouble cx) (cutDouble cy) m k := by
  show cutSumAux cx cy (2*k) (2*m) (2*m)
     = cutSumAux (cutDouble cx) (cutDouble cy) k (2*m) (2*m)
  rw [cutSumAux_cutDouble]

/-- **cutDouble distributes over cutSum** (cutEq, PURE). -/
theorem cutDouble_cutSum (cx cy : Nat → Nat → Bool) :
    cutEq (cutDouble (cutSum cx cy)) (cutSum (cutDouble cx) (cutDouble cy)) :=
  cutDouble_cutSum_at cx cy

/-- **cutDouble distributes over cutMid**, pointwise (PURE).
    Composes cutDouble_cutSum_at with cutDouble_cutHalf_comm. -/
theorem cutDouble_cutMid_at (cx cy : Nat → Nat → Bool) (m k : Nat) :
    cutDouble (cutMid cx cy) m k
    = cutMid (cutDouble cx) (cutDouble cy) m k := by
  show cutHalf (cutSum cx cy) m (2*k)
     = cutHalf (cutSum (cutDouble cx) (cutDouble cy)) m k
  show cutSum cx cy (2*m) (2*k)
     = cutSum (cutDouble cx) (cutDouble cy) (2*m) k
  exact cutDouble_cutSum_at cx cy (2*m) k

/-- **cutDouble distributes over cutMid** (cutEq, PURE).
    Composes cutDouble_cutSum with cutDouble_cutHalf_comm. -/
theorem cutDouble_cutMid (cx cy : Nat → Nat → Bool) :
    cutEq (cutDouble (cutMid cx cy)) (cutMid (cutDouble cx) (cutDouble cy)) :=
  cutDouble_cutMid_at cx cy

end E213.Lib.Math.Real213.Mul.CutDouble
