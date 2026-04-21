import Lean

/-!
# Tactic: `#verify_r4`

A command-level diagnostic that attempts to synthesise an
`E213.Meta.R4Codomain α` instance for a given type `α` and
reports whether the spec is satisfied.

This does **not** re-prove anything — it merely asks Lean's
typeclass machinery whether an instance has been registered
in the current environment, and prints a diagnostic.

Useful as a sanity-check when expanding the Lens catalogue:
after declaring a new `R4Codomain` instance, `#verify_r4
MyType` confirms it is reachable by the synthesis engine.

## Usage

```
open E213.Tactic
#verify_r4 ZI          -- ✓ R4Codomain ZI admitted
#verify_r4 Z2          -- ✓ R4Codomain Z2 admitted
#verify_r4 ZOmega      -- ✓ R4Codomain ZOmega admitted
#verify_r4 (ZSqrt 3)   -- ✓ R4Codomain (ZSqrt 3) admitted
```

## Scope

The command imports only `Lean` (for metaprogramming API).
At client invocation, the client must already have imported
`E213.Meta.SelfRecognising` and the target instance module.
This keeps `#verify_r4` free of Firmware rebuild cost.
-/

namespace E213.Tactic

open Lean Elab Command Meta

scoped syntax (name := verifyR4) "#verify_r4 " term : command

@[command_elab verifyR4]
def elabVerifyR4 : CommandElab := fun stx => do
  match stx with
  | `(#verify_r4 $α:term) => do
    liftTermElabM do
      let αExpr ← Term.elabTerm α none
      let αSort ← inferType αExpr
      unless αSort.isType do
        throwError "expected a type, got {αExpr} : {αSort}"
      let clsName : Name := `E213.Meta.R4Codomain
      let clsExpr := mkApp (mkConst clsName) αExpr
      let result ← synthInstance? clsExpr
      match result with
      | some _ =>
        logInfo m!"✓ R4Codomain {αExpr} admitted"
      | none =>
        throwError m!"✗ R4Codomain {αExpr} : no instance found"
  | _ => throwUnsupportedSyntax

end E213.Tactic
