import E213.Lib.Math.Analysis.Cauchy.ZeroRunNonHolonomic
import E213.Lib.Math.Analysis.Cauchy.SecondCasoratian
import E213.Meta.Int213.PolyIntMTactic

/-!
# C-finite ⟹ P-recursive (`HomogRec`) — closing the hierarchy

The merged divergence-depth / Casoratian thread studies **constant-coefficient** linear
recurrences: `CassiniDepthFloor` the order-2 orbit `s(n+2) = p·s(n+1) − q·s(n)`,
`SecondCasoratian` the order-3 `s(n+3) = a·s(n+2) + b·s(n+1) + c·s(n)` (Tribonacci).  These are
the **C-finite** sequences.  This file places them inside the **P-recursive** class
`ZeroRunNonHolonomic.HomogRec` that the non-holonomicity witnesses escape — a constant-coefficient
recurrence *is* a homogeneous finite-window recurrence (constant `lead = 1`, linear `R` vanishing
on the zero window).

So the hierarchy is now connected end to end:

> polynomial (`finite_depthZ_iff`) ⊆ **C-finite** (`order2/3_homogRec`) ⊆ **P-recursive**
> (`HomogRec`) ⊊ non-holonomic (`zero_run_not_homogRec`, `tm_morse_not_autoRec`, …).

Concretely: the golden/Lucas orbit and **Tribonacci** (the `SecondCasoratian` witness) are
`HomogRec` — *holonomic*, the opposite pole from Thue–Morse, which escapes.
-/

namespace E213.Lib.Math.Analysis.Cauchy.CFiniteHomogRec

open E213.Lib.Math.Analysis.Cauchy.ZeroRunNonHolonomic (HomogRec)
open E213.Lib.Math.Analysis.Cauchy.SecondCasoratian (trib trib_rec)

/-- **Order-2 C-finite ⟹ `HomogRec`.**  `s(n+2) = p·s(n+1) − q·s(n)` is a homogeneous
    order-2 window recurrence: `lead ≡ 1`, `R n w = p·w 1 − q·w 0` (linear, vanishes on zeros). -/
theorem order2_homogRec (p q : Int) (s : Nat → Int)
    (hrec : ∀ n, s (n + 2) = p * s (n + 1) - q * s n) : HomogRec s := by
  refine ⟨2, fun _ => 1, fun _ w => p * w 1 - q * w 0, 0, ?_, ?_, ?_⟩
  · intro n _; show (1 : Int) ≠ 0; decide
  · intro n w hw
    show p * w 1 - q * w 0 = 0
    rw [hw 1 (by decide), hw 0 (by decide),
        E213.Meta.Int213.PolyIntM.mul_zeroZ, E213.Meta.Int213.PolyIntM.mul_zeroZ]
    decide
  · intro n
    show (1 : Int) * s (n + 2) = p * s (n + 1) - q * s n
    rw [E213.Meta.Int213.mul_comm, E213.Meta.Int213.mul_one]; exact hrec n

/-- **Order-3 C-finite ⟹ `HomogRec`.**  `s(n+3) = a·s(n+2) + b·s(n+1) + c·s(n)`. -/
theorem order3_homogRec (a b c : Int) (s : Nat → Int)
    (hrec : ∀ n, s (n + 3) = a * s (n + 2) + b * s (n + 1) + c * s n) : HomogRec s := by
  refine ⟨3, fun _ => 1, fun _ w => a * w 2 + b * w 1 + c * w 0, 0, ?_, ?_, ?_⟩
  · intro n _; show (1 : Int) ≠ 0; decide
  · intro n w hw
    show a * w 2 + b * w 1 + c * w 0 = 0
    rw [hw 2 (by decide), hw 1 (by decide), hw 0 (by decide),
        E213.Meta.Int213.PolyIntM.mul_zeroZ, E213.Meta.Int213.PolyIntM.mul_zeroZ,
        E213.Meta.Int213.PolyIntM.mul_zeroZ]
    decide
  · intro n
    show (1 : Int) * s (n + 3) = a * s (n + 2) + b * s (n + 1) + c * s n
    rw [E213.Meta.Int213.mul_comm, E213.Meta.Int213.mul_one]; exact hrec n

/-- ★ **Tribonacci is `HomogRec`** — the `SecondCasoratian` order-3 witness is *holonomic*, the
    opposite pole from Thue–Morse (which escapes every finite-state machine). -/
theorem trib_homogRec : HomogRec trib := order3_homogRec 1 1 1 trib trib_rec

end E213.Lib.Math.Analysis.Cauchy.CFiniteHomogRec
