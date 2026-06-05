import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Binomial
import E213.Lib.Math.NumberSystems.Real213.ExpLog.CutFactorial
import E213.Meta.Nat.PolyNatMTactic

/-!
# `choose` ↔ factorial bridge (∅-axiom)

The combinatorial `choose` (Pascal recurrence) and the analytic `factorial` are the same number:

  `C(k+j, k) · k! · j! = (k+j)!`     (`choose_mul_factorials`)

equivalently `C(n, k) = n! / (k! (n−k)!)` cleared of division (with `n = k+j`, `n−k = j`, so no
`Nat`-subtraction).  Proven from the absorption identity `choose_succ_mul`
(`(k+1)·C(n+1,k+1) = (n+1)·C(n,k)`) by induction on `k`: multiply the goal by `k+1`, rewrite the
head `choose` via `choose_succ_mul` and `(k+1)! = (k+1)·k!`, apply the IH, and cancel `k+1`.

This is the bridge the **exp functional equation** needs: the `n`-th Taylor coefficient of
`exp(a+b)`, namely `(a+b)ⁿ/n!`, equals the Cauchy convolution `Σ_{j+k=n} (aʲ/j!)(bᵏ/k!)` of the
`exp(a)` and `exp(b)` coefficients — because cross-multiplying by `n!` turns the convolution into
`Σ_{j} C(n,j) aʲ bⁿ⁻ʲ = (a+b)ⁿ` (the binomial theorem), using exactly `C(n,j)·j!·(n−j)! = n!`.

All zero-axiom.
-/

namespace E213.Lib.Math.NumberTheory.DyadicFSM.FLT.ChooseFactorial

open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Binomial
  (choose choose_zero_right choose_succ_mul)
open E213.Lib.Math.NumberSystems.Real213.ExpLog.CutFactorial (factorial factorial_succ factorial_pos)

/-- ★★★ **`choose` ↔ factorial bridge**: `C(k+j, k) · (k! · j!) = (k+j)!`.

    The division-free form of `C(n,k) = n!/(k!(n−k)!)` (with `n = k+j`).  Induction on `k` via the
    absorption identity `choose_succ_mul`. -/
theorem choose_mul_factorials :
    ∀ (k j : Nat), choose (k + j) k * (factorial k * factorial j) = factorial (k + j)
  | 0, j => by
    rw [Nat.zero_add, choose_zero_right, show factorial 0 = 1 from rfl,
        Nat.one_mul, Nat.one_mul]
  | k + 1, j => by
    have ih : choose (k + j) k * (factorial k * factorial j) = factorial (k + j) :=
      choose_mul_factorials k j
    apply Nat.eq_of_mul_eq_mul_left (Nat.zero_lt_succ k)
    -- goal: (k+1) * (choose ((k+1)+j) (k+1) * (factorial (k+1) * factorial j))
    --     = (k+1) * factorial ((k+1)+j)
    rw [Nat.succ_add k j, factorial_succ k, factorial_succ (k + j)]
    -- normalise the head `(k+1)·choose ((k+j)+1) (k+1)` via choose_succ_mul, then reorganise
    have key : (k + 1) * (choose ((k + j) + 1) (k + 1) * ((k + 1) * factorial k * factorial j))
        = ((k + j) + 1) * (k + 1) * (choose (k + j) k * (factorial k * factorial j)) := by
      have hc : (k + 1) * choose ((k + j) + 1) (k + 1) = ((k + j) + 1) * choose (k + j) k :=
        choose_succ_mul (k + j) k
      calc (k + 1) * (choose ((k + j) + 1) (k + 1) * ((k + 1) * factorial k * factorial j))
          = ((k + 1) * choose ((k + j) + 1) (k + 1)) * ((k + 1) * factorial k * factorial j) := by
            ring_nat
        _ = (((k + j) + 1) * choose (k + j) k) * ((k + 1) * factorial k * factorial j) := by
            rw [hc]
        _ = ((k + j) + 1) * (k + 1) * (choose (k + j) k * (factorial k * factorial j)) := by
            ring_nat
    rw [key, ih,
        ← E213.Tactic.NatHelper.mul_assoc (k + 1) (k + j + 1) (factorial (k + j)),
        Nat.mul_comm (k + 1) (k + j + 1)]

/-- ★★ **`choose` symmetry**: `C(k+j, k) = C(k+j, j)`.  Both equal `(k+j)!/(k!·j!)`; cancel the
    common positive factor `k!·j!` from the two instances of the bridge. -/
theorem choose_symm (k j : Nat) : choose (k + j) k = choose (k + j) j := by
  have h1 := choose_mul_factorials k j
  have h2 := choose_mul_factorials j k
  rw [Nat.add_comm j k, Nat.mul_comm (factorial j) (factorial k)] at h2
  have heq : choose (k + j) k * (factorial k * factorial j)
           = choose (k + j) j * (factorial k * factorial j) := h1.trans h2.symm
  exact Nat.eq_of_mul_eq_mul_right
    (Nat.mul_pos (factorial_pos k) (factorial_pos j)) heq

end E213.Lib.Math.NumberTheory.DyadicFSM.FLT.ChooseFactorial
