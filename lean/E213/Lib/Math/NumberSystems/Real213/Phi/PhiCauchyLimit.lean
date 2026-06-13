import E213.Lib.Math.NumberSystems.Real213.Phi.FibCassiniNat
import E213.Lib.Math.Analysis.CauchyComplete

/-!
# PhiCauchyLimit — φ as the Cauchy-complete limit object

`PhiAsCut` gave φ as a single closed-form `ValidCut` (`phiCut`).  `FibCassiniNat`
proved the rational Fibonacci/Pell convergents climb to it and, past an honest
modulus, the convergent cut value **equals** `phiCut` exactly
(`cs_eq_phiCut`).  This file assembles the missing direction: φ built **as** the
limit object of the convergent sequence through the `CauchyCutSeq` machinery
(`Analysis/CauchyComplete`).

The convergent cut sequence — `fun i m k => decide (fib(2i+2)·k ≤ fib(2i+1)·m)`
— is the 213-native rational Pell convergent `fib(2i+2)/fib(2i+1)` read as a
Cut.  It is assembled into a `CauchyCutSeq` with explicit modulus `N(m,k) = 2k`,
and its `.limit` is proved **definitionally equal to `phiCut`** — not merely
`CutEquiv`, but the same `Nat → Nat → Bool`.

So φ has now been constructed two ways that agree on the nose:
  * **directly** — `PhiAsCut.phiCut`, the closed-form decidable cut, and
  * **as a limit** — `phiConvergentSeq.limit`, the Cauchy-complete limit of the
    rational convergents.

`phiCauchy_limit_eq_phiCut` is the bridge: the residue's irrational limit-ratio
signature is the *same* 213-native object whether pinned closed-form or built by
completion.  All ∅-axiom.
-/

namespace E213.Lib.Math.NumberSystems.Real213.Phi.PhiCauchyLimit

open E213.Lib.Math.Algebra.Mobius213.Px.FibonacciAtomicLock (fib)
open E213.Lib.Math.Analysis.CauchyComplete (CauchyCutSeq)
open E213.Lib.Math.NumberSystems.Real213.Phi.FibCassiniNat (cs_eq_phiCut)

/-- **The convergent cut sequence**: layer `i` reads the Pell convergent
    `fib(2i+2)/fib(2i+1)` as a Cut, `decide (fib(2i+2)·k ≤ fib(2i+1)·m)`.  The
    213-native rational sequence whose limit is φ. -/
def convergentCS (i m k : Nat) : Bool :=
  decide (fib (2 * i + 2) * k ≤ fib (2 * i + 1) * m)

/-- **φ as a Cauchy sequence of cuts** — the convergent cut sequence with the
    honest Archimedean modulus `N(m,k) = 2k`.  Past `2k` the value is constant
    (`cs_eq_phiCut`), so the `cauchy` field is immediate: any two tail indices
    both equal `phiCut m k`. -/
def phiConvergentSeq : CauchyCutSeq where
  cs := convergentCS
  N := fun _ k => 2 * k
  cauchy := by
    intro m k i j hi hj
    show convergentCS i m k = convergentCS j m k
    unfold convergentCS
    rw [cs_eq_phiCut i m k hi, cs_eq_phiCut j m k hj]

/-- ★★★ **φ's Cauchy-complete limit IS `phiCut`.**  The limit object extracted
    from the convergent Cauchy sequence — `phiConvergentSeq.limit` — equals the
    closed-form golden-ratio cut `phiCut` as the very same `Nat → Nat → Bool`.

    This closes the limit-ratio reading both ways: φ pinned directly as one
    decidable cut (`PhiAsCut.phiCut`) and φ built by Cauchy completion of the
    rational Pell convergents land on the *identical* 213-native object.  The
    residue's irrational signature is one Cut, however it is approached.
    (Pointwise — a function-level `=` would route through `funext`, which pulls
    `Quot.sound`; the pointwise statement is the ∅-axiom form and carries the
    same content for a `Nat → Nat → Bool` cut.)  PURE. -/
theorem phiCauchy_limit_eq_phiCut (m k : Nat) :
    phiConvergentSeq.limit m k = E213.Lib.Math.NumberSystems.Real213.Phi.PhiAsCut.phiCut m k := by
  show convergentCS (2 * k) m k = E213.Lib.Math.NumberSystems.Real213.Phi.PhiAsCut.phiCut m k
  unfold convergentCS
  exact cs_eq_phiCut (2 * k) m k (Nat.le_refl _)

end E213.Lib.Math.NumberSystems.Real213.Phi.PhiCauchyLimit
