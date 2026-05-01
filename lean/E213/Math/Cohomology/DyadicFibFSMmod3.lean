import E213.Math.Cohomology.Dyadic.ArithFSMtoBitFSM
import E213.Math.Cohomology.DyadicConcretePellSig

/-!
# Fibonacci ArithFSM mod 3 — period 8 (INERT case, parallel to Pell)

Fibonacci recurrence: F_{k+2} = F_{k+1} + F_k with F_0 = 0, F_1 = 1.
State (a, b) = (F_k, F_{k+1}); step (a, b) → (b, a+b).
Output: (a == 1) — bit signal indicating Fibonacci value 1.

Discriminant Δ = 5 (since x² - x - 1 = 0).

Pisano formula for Fibonacci:
  legendre(5, p) = 0 (ramified)  ⇒  π(p) = 4p
  legendre(5, p) = 1 (split, QR) ⇒  π(p) = p - 1
  legendre(5, p) = 2 (inert, NQR) ⇒  π(p) = 2(p + 1)

3 mod 5 = 3, NQR, INERT.  Predict: 2(3+1) = 8.  TIGHT.

This is a parallel construction to the Pell ArithFSM family — same
Galois-theoretic Legendre lens, different Pisano formula.
Establishes the Fibonacci-Pisano predictor as a *new structural
identity* in the 213 atomic framework.
-/

namespace E213.Math.Cohomology.DyadicConjecture

/-- Fibonacci-style FSM mod 3. -/
def fibFSMmod3 : ArithFSM2 3 where
  init := (⟨0, by decide⟩, ⟨1, by decide⟩)
  step p := let (a, b) := p
    (b, ⟨(a.val + b.val) % 3, Nat.mod_lt _ (by decide)⟩)
  out p := p.1.val == 1

/-- ★★★ Fibonacci mod-3 run cycles with TIGHT period 8. -/
theorem fibFSMmod3_run_period_8 :
    ∀ k, fibFSMmod3.run (k + 8) = fibFSMmod3.run k := by
  intro k
  induction k with
  | zero => decide
  | succ k' ih =>
    show fibFSMmod3.step (fibFSMmod3.run (k' + 8))
        = fibFSMmod3.step (fibFSMmod3.run k')
    rw [ih]

/-- ★★★★ Fibonacci mod-3 bits cycle with TIGHT period 8. -/
theorem fibFSMmod3_bits_period_8 :
    ∀ k, fibFSMmod3.bits (k + 8) = fibFSMmod3.bits k := by
  intro k
  show fibFSMmod3.out (fibFSMmod3.run (k + 8))
      = fibFSMmod3.out (fibFSMmod3.run k)
  rw [fibFSMmod3_run_period_8]

/-- ★★★★★ Fibonacci mod-3 signature has period 8 from step 1
    (pre-period 1; init bit is `false`, distinct from base sig 0). -/
theorem fibFSMmod3_signature_period_8_from_1 :
    ∀ k, k ≥ 1 →
      signature fibFSMmod3.bits (k + 8)
        = signature fibFSMmod3.bits k :=
  signature_period_of_bits_period_and_anchor_from
    fibFSMmod3.bits 8 1 fibFSMmod3_bits_period_8 (by decide)

end E213.Math.Cohomology.DyadicConjecture
