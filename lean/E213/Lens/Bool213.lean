import E213.Lens.Bool213.Raw
import E213.Lens.Bool213.System
import E213.Lens.Bool213.SelfReferenceForms

/-! Spec-as-code entry point for `E213.Lens.Bool213`.

  213-native Boolean — Raw-encoded closed-universe Bool.  Three
  modules:

    * `Raw`     — Method A 카타모피즘 (T = Raw.a, F = Raw.b).
                  `booleanProj := Raw.fold T F and` — closed-Raw
                  codomain catamorphism, Raw-internal vertical
                  projection onto the two-element form {T, F}.
                  not / and / boolValue / fixed-point characterisation.
    * `System`  — meta (T, F) pattern: any distinct Raw pair is a
                  valid system; system iso preserves not / and.
                  Parallel to Nat213's `NumberingSystem`.
    * `SelfReferenceForms` — the two structural forms of Raw
                  self-reference (`05_no_exterior` §5.2): the Bool
                  `not` is an involution (period 2) with no fixed
                  point on its values (`bool_not_no_fixed_point`,
                  the liar oscillation), contrasted with the Nat-style
                  Lambek period-1 self-fixed-point + well-founded
                  descent (`self_reference_two_forms`).

  Raw + catamorphism = Lens-layer product.  All theorems ∅-axiom.
-/
