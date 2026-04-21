import Lean

/-!
# Tactic: `derive_r4_codomain`

A `command_elab` that synthesises the 13-field
`instance : E213.Meta.R4Codomain α` declaration by naming
convention.

The elab does **not** import `E213.Meta.SelfRecognising` — it
only generates *syntax* that references the class.  At the
client site (where `derive_r4_codomain` is invoked), the
import must already be in place.  This avoids transitively
rebuilding `Firmware/Raw.lean` when the elab itself is
edited.

## Usage

```
open E213.Tactic
derive_r4_codomain ZI with_bases I negI
```

This expands to:
```
instance : R4Codomain ZI where
  base_a := ZI.I
  base_b := ZI.negI
  combine := ZI.mul
  combine_comm := ZI.mul_comm
  base_a_ne_zero := by intro h; cases h
  base_b_ne_zero := by intro h; cases h
  no_zero_div := ZI.no_zero_div
  conj := ZI.conj
  conj_involution := ZI.conj_conj
  conj_ne_id := ZI.conj_ne_id
  conj_dist := ZI.conj_mul
  conj_swap_a := ZI.conj_I
  conj_swap_b := ZI.conj_negI
```

## Naming convention required

For `derive_r4_codomain α with_bases b₁ b₂` the namespace `α`
must contain (in addition to the type itself):
- `α.b₁`, `α.b₂` — base values
- `α.mul` — combine
- `α.conj` — involution
- `α.mul_comm`, `α.no_zero_div`, `α.conj_conj`, `α.conj_ne_id`,
  `α.conj_mul`
- `α.conj_b₁`, `α.conj_b₂` — `conj` action on bases
-/

namespace E213.Tactic

open Lean Elab Command

scoped syntax (name := deriveR4Codomain)
  "derive_r4_codomain " ident "with_bases" ident ident : command

end E213.Tactic

namespace E213.Tactic

open Lean Elab Command

@[command_elab deriveR4Codomain]
def elabDeriveR4 : CommandElab := fun stx => do
  match stx with
  | `(derive_r4_codomain $α:ident with_bases $b1:ident $b2:ident) => do
    let αN := α.getId
    let mk (s : Name) := mkIdentFrom α (αN ++ s)
    let baseA  := mk b1.getId
    let baseB  := mk b2.getId
    let mul    := mk `mul
    let conj   := mk `conj
    let mulC   := mk `mul_comm
    let nzd    := mk `no_zero_div
    let cConj  := mk `conj_conj
    let cNeId  := mk `conj_ne_id
    let cMul   := mk `conj_mul
    let cSwapA := mk (`conj ++ b1.getId)
    let cSwapB := mk (`conj ++ b2.getId)
    let cmd ← `(instance : E213.Meta.R4Codomain $α where
                  base_a          := $baseA
                  base_b          := $baseB
                  combine         := $mul
                  combine_comm    := $mulC
                  base_a_ne_zero  := by intro h; cases h
                  base_b_ne_zero  := by intro h; cases h
                  no_zero_div     := $nzd
                  conj            := $conj
                  conj_involution := $cConj
                  conj_ne_id      := $cNeId
                  conj_dist       := $cMul
                  conj_swap_a     := $cSwapA
                  conj_swap_b     := $cSwapB)
    elabCommand cmd
  | _ => throwUnsupportedSyntax

end E213.Tactic
