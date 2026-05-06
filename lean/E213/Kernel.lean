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
import E213.Kernel.Tactic
import E213.Kernel.Term

/-! Spec-as-code entry point for `E213.Kernel`.

  Bare-metal type-theory layer — lowest in the ARCHITECTURE.md
  vertical stack.

  ## Core

    * `Term`              — deep-embedded 213 term type
    * `API`               — public surface
    * `Compare`,
      `Decide`,
      `Sound`             — discharge primitives
    * `Pair`,
      `Rat`               — Pair / Rat reflection types
    * `MonomialAxioms`    — monomial-evaluation primitive set
    * `Demo`              — demonstration / smoke-test wrapper

  ## Capability witnesses (Cap_*)

    * `Cap_MathArithmetic`,
      `Cap_AtomicComplexity`,
      `Cap_PeriodicTable`,
      `Cap_PhysicsAtomicIE`,
      `Cap_PhysicsBrackets`,
      `Cap_PhysicsFalsifiers`,
      `Cap_PhysicsObservables` — each capability has a Kernel
      witness verifying it lands at this layer.

  ## Sub-cluster

    * `Tactic/`           — 213-native tactic library (Nat213,
                            Mod213, Fin213, Pow213, Omega213,
                            QuadNorm + Test/)
-/
