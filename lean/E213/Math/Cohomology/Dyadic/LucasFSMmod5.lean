import E213.Math.Cohomology.Dyadic.ArithFSM.ToBitFSM
import E213.Math.Cohomology.Dyadic.ConcretePellSig

/-!
# Lucas ArithFSM mod 5 — period 4 (RAMIFIED, KEY divergence from Fibonacci)

Lucas recurrence: L_0 = 2, L_1 = 1, L_{n+1} = L_n + L_{n-1}.
Same recurrence as Fibonacci but DIFFERENT initial conditions.

At p=5 (RAMIFIED for Δ=5, since x²-x-1 ≡ (x-3)² mod 5):
  - Lucas period = 4   (= p-1)
  - Fibonacci period = 20 (= 4p)

This divergence is purely from initial conditions interacting with
the double-root regularization at ramification:
  L_n = α^n + β^n     (regular at α=β: L_n = 2·α^n, period = ord(α))
  F_n = (α^n-β^n)/(α-β) (singular: F_n = n·α^(n-1), period × p factor)

Lucas-Pisano formula at ramification: π(p) = p - 1 (NOT 4p like Fib).
At split / inert: same as Fib.

This makes Lucas a third recurrence family in 213's Pisano-CRT
framework, distinct from Pell and Fibonacci.
-/

namespace E213.Math.Cohomology.Dyadic.LucasFSMmod5

open E213.Math.Cohomology.Dyadic.ArithFSM (ArithFSM2)


/-- Lucas-style FSM mod 5. -/
def lucasFSMmod5 : ArithFSM2 5 where
  init := (⟨2, by decide⟩, ⟨1, by decide⟩)
  step p := let (a, b) := p
    (b, ⟨(a.val + b.val) % 5, Nat.mod_lt _ (by decide)⟩)
  out p := p.1.val == 1

/-- Lucas mod-5 first values: 2, 1, 3, 4, 2, 1, 3, 4, ... (period 4). -/
theorem lucasFSMmod5_first6 :
    lucasFSMmod5.bits 0 = false ∧ lucasFSMmod5.bits 1 = true
    ∧ lucasFSMmod5.bits 4 = false ∧ lucasFSMmod5.bits 5 = true := by decide

/-- ★★★★ Lucas mod-5 run cycles with TIGHT period 4. -/
theorem lucasFSMmod5_run_period_4 :
    ∀ k, lucasFSMmod5.run (k + 4) = lucasFSMmod5.run k := by
  intro k
  induction k with
  | zero => decide
  | succ k' ih =>
    show lucasFSMmod5.step (lucasFSMmod5.run (k' + 4))
        = lucasFSMmod5.step (lucasFSMmod5.run k')
    rw [ih]

/-- ★★★★★ Lucas mod-5 bits cycle with TIGHT period 4. -/
theorem lucasFSMmod5_bits_period_4 :
    ∀ k, lucasFSMmod5.bits (k + 4) = lucasFSMmod5.bits k := by
  intro k
  show lucasFSMmod5.out (lucasFSMmod5.run (k + 4))
      = lucasFSMmod5.out (lucasFSMmod5.run k)
  rw [lucasFSMmod5_run_period_4]

end E213.Math.Cohomology.Dyadic.LucasFSMmod5
