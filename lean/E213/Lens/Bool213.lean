import E213.Lens.Bool213.Raw
import E213.Lens.Bool213.System

/-! Spec-as-code entry point for `E213.Lens.Bool213`.

  213-native Boolean — Raw-encoded closed-universe Bool.  Two
  modules:

    * `Raw`     — Method A 카타모피즘 (T = Raw.a, F = Raw.b).
                  `booleanProj := Raw.fold T F and` — closed-Raw
                  codomain catamorphism, Raw-internal vertical
                  projection onto the two-element form {T, F}.
                  not / and / boolValue / fixed-point characterisation.
    * `System`  — meta (T, F) pattern: any distinct Raw pair is a
                  valid system; system iso preserves not / and.
                  Parallel to Nat213's `NumberingSystem`.

  Raw + catamorphism = Lens-layer product.  All theorems ∅-axiom.
-/
