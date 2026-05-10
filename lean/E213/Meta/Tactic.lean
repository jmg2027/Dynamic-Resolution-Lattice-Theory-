import E213.Meta.Tactic.DeriveConjugationCodomain
import E213.Meta.Tactic.PureGuard
import E213.Meta.Tactic.PureGuardTest
import E213.Meta.Tactic.Test.VerifyConjugationTest
import E213.Meta.Tactic.VerifyConjugation

/-! Spec-as-code entry point for `E213.Meta.Tactic`.

  Meta-level tactics that operate at the codomain-typeclass
  layer (`Meta/SelfRecognising.lean`).

  ## Code-generators

    * `DeriveConjugationCodomain` — generates a
      `ConjugationCodomain α` instance for a given α from the
      bare `mul / conj / base_a / base_b / mul_comm / no_zero_div /
      conj_*` lemmas.  Used by `Math/CayleyDickson/{ZI,Z2,ZOmega}
      Instance.lean`.
    * `VerifyConjugation` — `#verify_conjugation α` command-level
      diagnostic that checks an instance is reachable by
      typeclass synthesis.

  ## Native / pure guards

    * `NativeGuard`,
      `NativeGuardTest` — block use of the kernel-bypass
                          ``native``-form ``decide`` variant via
                          a custom-error tactic.
    * `PureGuard`,
      `PureGuardTest`   — pure-discipline guard checking the
                          ∅-axiom standard at compile time.

  ## Tests

    * `Test.VerifyConjugationTest` — round-trip verification of
                                     the six concrete codomain
                                     witnesses (ZI / Z2 / ZOmega
                                     / ZSqrt 3 / ZSqrt 5 / ZSqrt 7).
-/
