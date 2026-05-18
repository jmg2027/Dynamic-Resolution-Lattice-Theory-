import E213.Lib.Math.DyadicFSM.Legendre
import E213.Lib.Math.DyadicFSM.ArithFSM.ToBitFSM
import E213.Lib.Math.DyadicFSM.ConcretePellSig

import E213.Lib.Math.DyadicFSM.ArithFSM
/-!
# Pell proper (discriminant 8) — Legendre lens framework

Pell proper recurrence: P_{n+1} = 2 P_n + P_{n-1}, P_0 = 0, P_1 = 1.
Companion matrix M = [[2,1],[1,0]], characteristic polynomial
λ² - 2λ - 1, discriminant Δ = 4 + 4 = 8.

The Legendre lens (8/p) governs the Pisano-style period:
  - split (8/p = 1):    π(p) | p - 1
  - inert (8/p = -1):   π(p) | 2(p+1)
  - ramified (8/p = 0): special (only p = 2)

Note the formulas differ from the Pell-Fibonacci-squared case
([[2,1],[1,1]], Δ=5):
  - In Δ=5: split → (p-1)/2, inert → p+1, ramified → 2p
  - In Δ=8: split → p-1,     inert → 2(p+1)

This shift reflects that Pell-proper sequences are NOT Fibonacci-
squared — eigenvalues 1±√2 (units of ℤ[√2]) instead of φ²/ψ².
-/

namespace E213.Lib.Math.DyadicFSM.Pell.Proper

open E213.Lib.Math.DyadicFSM.ArithFSM (ArithFSM2)
open E213.Lib.Math.DyadicFSM.Legendre.V213 (legendre213)


/-- Pell proper FSM mod n: state (a_n, a_{n-1}) → (a_{n+1}, a_n). -/
def pellProperFSMmod (n : Nat) (hn : 0 < n) : ArithFSM2 n where
  init := (⟨1 % n, Nat.mod_lt _ hn⟩, ⟨0, hn⟩)
  step p := let (a, b) := p
    (⟨(2 * a.val + b.val) % n, Nat.mod_lt _ hn⟩,
     ⟨a.val % n, Nat.mod_lt _ hn⟩)
  out p := p.1.val == 1

/-- 213-native Pisano predictor for Pell proper (D = 8). -/
def pisano_predict_proper (p : Nat) (hp : 1 < p) : Nat :=
  let leg := (legendre213 8 p hp).val
  if leg = 0 then 2 * p          -- ramified (only p = 2)
  else if leg = 1 then p - 1     -- split
  else 2 * (p + 1)               -- inert

end E213.Lib.Math.DyadicFSM.Pell.Proper
