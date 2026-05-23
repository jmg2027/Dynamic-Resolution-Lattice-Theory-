import E213.Meta.Tactic.DeriveConjugationCodomain
import E213.Meta.Tactic.Fin213
import E213.Meta.Tactic.Mod213
import E213.Meta.Tactic.NatHelper
import E213.Meta.Tactic.NativeGuard
import E213.Meta.Tactic.NativeGuardTest
import E213.Meta.Tactic.Omega213
import E213.Meta.Tactic.Pow213
import E213.Meta.Tactic.PureGuard
import E213.Meta.Tactic.PureGuardTest
import E213.Meta.Tactic.QuadNorm
import E213.Meta.Tactic.Test.QuadNormTest
import E213.Meta.Tactic.Test.VerifyConjugationTest
import E213.Meta.Tactic.VerifyConjugation

/-! Spec-as-code entry point for `E213.Meta.Tactic`.

  Meta layer tactics — Lean 4 와의 bridge.  Ring-independent
  per `ARCHITECTURE.md`.  Two families coexist:

  ## A. 213-native arithmetic tactics

  213-native replacements for Lean's `omega` / `simp` that bring
  zero hidden axioms.  Consumed by every ring above.

    * `NatHelper`  — `Nat`-arithmetic helpers (substitutes for
                     `omega` in many leaf-level proofs).
                     confusion with the `Nat213` *type*
                     (`Lens.Number.Nat213`).  Namespace
                     `E213.Tactic.NatHelper`.
    * `Mod213`     — modular-arithmetic decisions
    * `Fin213`     — `Fin n` index manipulation
    * `Pow213`     — power / exponent decisions
    * `Omega213`   — bracket-only `omega` replacement
    * `QuadNorm`   — `quad_norm` macro for Diophantus-style
                     polynomial-identity goals
    * `Test/QuadNormTest` — `quad_norm` regression tests

  Namespace is `E213.Tactic.*` — the short prefix is intentional
  for downstream use-sites (`omega213`, `nat_helper`, etc.) so the
  tactic names stay terse at proof-call sites.

  ## B. Codomain-typeclass meta-tactics

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
