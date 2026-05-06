import E213.Lib.Physics.Nuclear.Binding
import E213.Lib.Physics.Nuclear.Bridge
import E213.Lib.Physics.Nuclear.DeuteronBinding
import E213.Lib.Physics.Nuclear.MagicNumbers
import E213.Lib.Physics.Nuclear.MagicNumbersAtomic
import E213.Lib.Physics.Nuclear.Shells

/-! Spec-as-code entry point for `E213.Lib.Physics.Nuclear`.

  Nuclear-physics cluster — magic numbers, binding, shells.

  ## Files

    * `MagicNumbers`,
      `MagicNumbersAtomic`  — 2,8,20,28,50,82,126 exact (7/7)
    * `Shells`              — nuclear shell-model structure
    * `Binding`             — nuclear binding-energy terms
    * `DeuteronBinding`     — deuteron binding-energy specifically
    * `Bridge`              — cross-reference layer to Foundations
                              + Math.Cohomology
-/
