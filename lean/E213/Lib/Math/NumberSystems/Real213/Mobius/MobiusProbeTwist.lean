import E213.Lib.Math.NumberSystems.Real213.Mobius.Mobius213Equiv
import E213.Lib.Math.NumberSystems.Real213.Core.ValidCut
import E213.Meta.Nat.PureNat

/-!
# ProbeTwist — the P-twist on cut-probe coordinates, and its `NS−NT` invariant

A Real213 cut is queried at a rational probe `(m, k)` ("is the value `≤ m/k`?").
The two probe axes are not independent in 213: the Möbius matrix
`P = [[2,1],[1,1]]` — the same `P` whose orbit generates the Fibonacci/Pell
convergents (`Mobius213Equiv`) and whose `(NS, NT) = (3, 2)` signature runs through
the framework — **twists them into each other**,

    Pstep (m, k) = (2m + k,  m + k),

mixing the numerator axis `m` and the precision axis `k` (the two matrix columns).

This file makes precise what that twist does to a cut.  Pre-composing a cut with
the probe-twist,

    cutThroughP c  :=  fun m k => c (2m + k, m + k),

is "viewing the cut `c` through one application of `P` on the probe lattice".

  * **P preserves rational order on the probe** (`P_preserves_order`): if
    `m1/k1 ≤ m2/k2` then `P(m1,k1) ≤ P(m2,k2)` as rationals.  The proof's single
    inequality (`twist_ineq`) is governed by `det P = 2·1 − 1·1 = 1 = NS − NT`
    (`det_P_eq_NS_sub_NT`) — the twist is *orientation-preserving* exactly because
    its determinant is the positive atomic unit `NS − NT`.
  * Consequently **the twist preserves cut validity**: `cutThroughP` sends a
    `RatioCut` to a `RatioCut` (`cutThroughP_ratio`).  Viewing a real through the
    `P`-twist of its probe lattice is again a real.

Scope note (no overclaim): this records that the *probe lattice* the modulus lives
on carries the `(2,1;1,1)` two-axis twist whose invariant is `NS − NT = 1`.  It is
**not** a claim that every real's modulus "splits along 2/3" — that would be
stereotype matching.  How individual reals sit on this lattice (their modulus
forms) is the separate, finer question of `Analysis/ModulusForm`.  What is proven
here is structural: the comparison lattice itself is `P`-twisted, two axes braided
by the `(NS,NT)` matrix, order-preserving by its `NS−NT` determinant.

All ∅-axiom.
-/

namespace E213.Lib.Math.NumberSystems.Real213.Mobius.MobiusProbeTwist

open E213.Lib.Math.NumberSystems.Real213.Mobius.Mobius213Equiv (Pstep)
open E213.Lib.Math.NumberSystems.Real213.Core.ValidCut (RatioCut)
open E213.Meta.Nat.PureNat (add_mul mul_assoc)

/-! ## §1 — the determinant invariant `NS − NT` -/

/-- ★ **`det P = NS − NT = 1`.**  `P = [[2,1],[1,1]]`, `det = 2·1 − 1·1 = 1`; with
    `(NS, NT) = (3, 2)`, `NS − NT = 1`.  The twist's orientation invariant is the
    213 atomic difference. -/
theorem det_P_eq_NS_sub_NT : 2 * 1 - 1 * 1 = 3 - 2 := by decide

/-! ## §2 — P preserves rational order on the probe (the `det > 0` content) -/

private theorem ac_lemma (a b : Nat) : a + (b + a) = b + (a + a) := by
  rw [Nat.add_comm b a, ← Nat.add_assoc, Nat.add_comm a a, Nat.add_comm (a+a) b]

/-- The cross-multiplied surplus stays ordered: from `m1·k2 ≤ m2·k1`,
    `k1·m2 + 2·(m1·k2) ≤ m1·k2 + 2·(m2·k1)`.  This is where `det P = 1 > 0`
    enters — the twisted inequality survives. -/
private theorem twist_ineq (m1 k1 m2 k2 : Nat) (h : m1*k2 ≤ m2*k1) :
    k1*m2 + 2*(m1*k2) ≤ m1*k2 + 2*(m2*k1) := by
  rw [Nat.two_mul, Nat.two_mul, Nat.mul_comm k1 m2]
  have step1 : m2*k1 + (m1*k2 + m1*k2) ≤ m2*k1 + (m2*k1 + m1*k2) :=
    Nat.add_le_add_left (Nat.add_le_add_right h _) _
  have step2 : m2*k1 + (m2*k1 + m1*k2) = m1*k2 + (m2*k1 + m2*k1) := by
    rw [Nat.add_comm (m2*k1) (m1*k2)]; exact ac_lemma (m2*k1) (m1*k2)
  exact Nat.le_trans step1 (Nat.le_of_eq step2)

private theorem expand (a b p q : Nat) :
    (a + b) * (p + q) = a*p + a*q + (b*p + b*q) := by
  rw [add_mul, Nat.mul_add, Nat.mul_add, Nat.add_assoc]

private theorem grp14_23 (w x y z : Nat) : w + x + (y + z) = (w + z) + (x + y) := by
  calc w + x + (y + z)
      = w + (x + (y + z)) := Nat.add_assoc w x (y+z)
    _ = w + (x + y + z)   := by rw [Nat.add_assoc x y z]
    _ = w + (z + (x + y)) := by rw [Nat.add_comm (x+y) z]
    _ = (w + z) + (x + y) := (Nat.add_assoc w z (x+y)).symm

/-- ★★★ **P preserves rational order on the probe.**  If `m1/k1 ≤ m2/k2`
    (cross-multiplied `m1·k2 ≤ m2·k1`), the twisted probes satisfy
    `P(m1,k1) ≤ P(m2,k2)`, i.e. `(2m1+k1)·(m2+k2) ≤ (2m2+k2)·(m1+k1)`.  The
    two-axis braid `(m,k) ↦ (2m+k, m+k)` is monotone on the rationals — its
    `det = 1 = NS − NT` makes it orientation-preserving. -/
theorem P_preserves_order (m1 k1 m2 k2 : Nat) (h : m1 * k2 ≤ m2 * k1) :
    (2*m1 + k1) * (m2 + k2) ≤ (2*m2 + k2) * (m1 + k1) := by
  rw [expand (2*m1) k1 m2 k2, expand (2*m2) k2 m1 k1,
      grp14_23 (2*m1*m2) (2*m1*k2) (k1*m2) (k1*k2),
      grp14_23 (2*m2*m1) (2*m2*k1) (k2*m1) (k2*k1)]
  have ecommon : 2*m1*m2 + k1*k2 = 2*m2*m1 + k2*k1 := by
    rw [mul_assoc 2 m1 m2, Nat.mul_comm m1 m2, ← mul_assoc 2 m2 m1, Nat.mul_comm k1 k2]
  rw [ecommon]
  apply Nat.add_le_add_left
  have eL : 2*m1*k2 + k1*m2 = k1*m2 + 2*(m1*k2) := by rw [mul_assoc 2 m1 k2, Nat.add_comm]
  have eR : 2*m2*k1 + k2*m1 = m1*k2 + 2*(m2*k1) := by
    rw [mul_assoc 2 m2 k1, Nat.add_comm, Nat.mul_comm k2 m1]
  rw [eL, eR]
  exact twist_ineq m1 k1 m2 k2 h

/-! ## §3 — the twist sends cuts to cuts -/

/-- **Viewing a cut through the `P`-twist of its probe**: `cutThroughP c m k =
    c (2m+k) (m+k)` — query `c` at the `P`-image of the probe. -/
def cutThroughP (c : Nat → Nat → Bool) : Nat → Nat → Bool :=
  fun m k => c (2*m + k) (m + k)

/-- ★★★ **The P-twist preserves cut validity.**  If `c` is a `RatioCut` (respects
    rational order, the defining property of a real-cut), so is `cutThroughP c`.
    The braid on the probe lattice carries reals to reals — order-preservation
    (`P_preserves_order`, i.e. `det = NS−NT > 0`) is exactly what `ratioMono`
    needs. -/
theorem cutThroughP_ratio (c : Nat → Nat → Bool) (hc : RatioCut c) :
    RatioCut (cutThroughP c) := by
  constructor
  intro m1 k1 m2 k2 hk1 hratio hcut
  show c (2*m2 + k2) (m2 + k2) = true
  apply hc.ratioMono (2*m1+k1) (m1+k1) (2*m2+k2) (m2+k2)
  · exact Nat.le_trans hk1 (Nat.le_add_left k1 m1)
  · exact P_preserves_order m1 k1 m2 k2 hratio
  · exact hcut

end E213.Lib.Math.NumberSystems.Real213.Mobius.MobiusProbeTwist
