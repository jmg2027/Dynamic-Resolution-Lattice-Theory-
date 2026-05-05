import E213.Kernel.API
import E213.Kernel.Cap_AtomicComplexity
import E213.Kernel.Cap_MathArithmetic
import E213.Kernel.Cap_PeriodicTable
import E213.Kernel.Cap_PhysicsAtomicIE
import E213.Kernel.Cap_PhysicsBrackets
import E213.Kernel.Cap_PhysicsFalsifiers
import E213.Kernel.Cap_PhysicsObservables
import E213.Kernel.Compare
import E213.Kernel.Decide
import E213.Kernel.Demo
import E213.Kernel.MonomialAxioms
import E213.Kernel.Pair
import E213.Kernel.Rat
import E213.Kernel.Sound
import E213.Kernel.Tactic.Fin213
import E213.Kernel.Tactic.Mod213
import E213.Kernel.Tactic.Nat213
import E213.Kernel.Tactic.Omega213
import E213.Kernel.Tactic.Pow213
import E213.Kernel.Tactic.QuadNorm
import E213.Kernel.Tactic.Test.QuadNormTest
import E213.Kernel.Term

/-! Spec-as-code entry point for `E213.Kernel` — kernel-tier modules.

  Bare-metal type theory layer (Kernel/): API, Cap_*, Compare/Decide/Sound discharge primitives, plus the `Tactic/` macro layer and `Tactic/Test/` self-tests. Lowest layer in the ARCHITECTURE.md vertical stack.

  ## Status

  23 files included.  0 files excluded
  (pre-existing breakage):

    (none)
-/
