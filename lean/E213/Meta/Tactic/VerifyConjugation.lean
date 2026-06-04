import Lean

/-!
# Tactic: `#verify_conjugation`

A command-level diagnostic that attempts to synthesise an
`E213.Meta.SelfRecognising.ConjugationCodomain α` instance for a given type
`α` and reports whether the spec is satisfied.

This does **not** re-prove anything — it merely asks Lean's
typeclass machinery whether an instance has been registered
in the current environment, and prints a diagnostic.

Useful as a sanity-check when expanding the Lens catalogue:
after declaring a new `ConjugationCodomain` instance,
`#verify_conjugation MyType` confirms it is reachable by the
synthesis engine.

## Usage

```
open E213.Tactic
#verify_conjugation ZI          -- ✓ ConjugationCodomain ZI admitted
#verify_conjugation Z2          -- ✓ ConjugationCodomain Z2 admitted
#verify_conjugation ZOmega      -- ✓ ConjugationCodomain ZOmega admitted
#verify_conjugation (ZSqrt 3)   -- ✓ ConjugationCodomain (ZSqrt 3) admitted
```

## Scope

The command imports only `Lean` (for metaprogramming API).
At client invocation, the client must already have imported
`E213.Meta.SelfRecognising` and the target instance module.
This keeps `#verify_conjugation` free of Theory rebuild cost.
-/

namespace E213.Tactic

open Lean Elab Command Meta

scoped syntax (name := verifyConjugation) "#verify_conjugation " term : command

@[command_elab verifyConjugation]
def elabVerifyConjugation : CommandElab := fun stx => do
  match stx with
  | `(#verify_conjugation $α:term) => do
    liftTermElabM do
      let αExpr ← Term.elabTerm α none
      let αSort ← inferType αExpr
      unless αSort.isType do
        throwError "expected a type, got {αExpr} : {αSort}"
      -- Synthesise `[Zero α]` explicitly, then apply ConjugationCodomain
      -- to both `α` and that instance argument.  Without the
      -- explicit Zero, `synthInstance?` would leave the
      -- instance-binder slot as a metavariable and silently
      -- fail on parametric types like `ZSqrt D`.
      let zeroCls ← Meta.mkAppM `Zero #[αExpr]
      let zeroInst? ← synthInstance? zeroCls
      match zeroInst? with
      | none =>
          throwError m!"✗ ConjugationCodomain {αExpr} : no `Zero {αExpr}` instance"
      | some zeroInst =>
          let clsExpr ← Meta.mkAppOptM
              `E213.Meta.SelfRecognising.ConjugationCodomain #[some αExpr, some zeroInst]
          let result ← synthInstance? clsExpr
          match result with
          | some _ =>
            logInfo m!"✓ ConjugationCodomain {αExpr} admitted"
          | none =>
            throwError m!"✗ ConjugationCodomain {αExpr} : no instance found"
  | _ => throwUnsupportedSyntax

end E213.Tactic
