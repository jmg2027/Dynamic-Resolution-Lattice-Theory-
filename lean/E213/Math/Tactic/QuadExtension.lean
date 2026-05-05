import Lean
import E213.Math.CayleyDickson.ZSqrtInstance

/-!
# Tactic: `quad_extension D` — parametric `ℤ[√-D]` one-liner

A command-level macro that registers a `ConjugationCodomain
(ZSqrt D)` instance for a positive natural `D`.  Equivalent to:

```
instance : E213.Meta.ConjugationCodomain (E213.Math.CayleyDickson.ZSqrt D) :=
  E213.Math.CayleyDickson.ZSqrt.conjugation_of_pos (by decide)
```

but reduces the per-D boilerplate to a single keyword + literal.

## Usage

```
open E213.Tactic
quad_extension 11       -- registers ConjugationCodomain (ZSqrt 11)
quad_extension 13       -- registers ConjugationCodomain (ZSqrt 13)
quad_extension 17       -- registers ConjugationCodomain (ZSqrt 17)
```

## Diagnostic

`D = 0` is rejected: `ℤ[√0] = ℤ` has no nontrivial involution
and therefore fails the swap-matching axiom (conj would equal
id).  Negative D is inexpressible at the `num` syntax level.

## Scope

Purely a convenience macro on top of the parametric
`ZSqrt.conjugation_of_pos` theorem.  Adds **no** new
mathematical content; the elaboration resolves to the same
`conjugation_of_pos` call at every site.
-/

namespace E213.Tactic

open Lean Elab Command

scoped syntax (name := quadExtension) "quad_extension " num : command

@[command_elab quadExtension]
def elabQuadExtension : CommandElab := fun stx => do
  match stx with
  | `(quad_extension $d:num) => do
      let dVal := d.getNat
      if dVal = 0 then
        throwError "quad_extension: D must be positive (got 0); \
                    ℤ[√0] = ℤ has no nontrivial involution, so the \
                    swap-matching axiom fails"
      let cmd ← `(command|
        instance : E213.Meta.ConjugationCodomain (E213.Math.CayleyDickson.ZSqrt $d) :=
          E213.Math.CayleyDickson.ZSqrt.conjugation_of_pos (by decide))
      elabCommand cmd
      logInfo m!"✓ quad_extension {dVal}: ConjugationCodomain (ZSqrt {dVal}) registered"
  | _ => throwUnsupportedSyntax

end E213.Tactic
