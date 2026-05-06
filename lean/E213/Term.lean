import E213.Term.API
import E213.Term.Cap_AtomicComplexity
import E213.Term.Cap_MathArithmetic
import E213.Term.Cap_PeriodicTable
import E213.Term.Cap_PhysicsAtomicIE
import E213.Term.Cap_PhysicsBrackets
import E213.Term.Cap_PhysicsFalsifiers
import E213.Term.Cap_PhysicsObservables
import E213.Term.Compare
import E213.Term.Decide
import E213.Term.Demo
import E213.Term.MonomialAxioms
import E213.Term.Pair
import E213.Term.Rat
import E213.Term.Sound
import E213.Term.Tactic
import E213.Term.Term

/-! Spec-as-code entry point for `E213.Term`.

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
