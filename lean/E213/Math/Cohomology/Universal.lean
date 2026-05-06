import E213.Math.Cohomology.Universal.Core
import E213.Math.Cohomology.Universal.Prop
import E213.Math.Cohomology.Universal.Prop31
import E213.Math.Cohomology.Universal.Prop41
import E213.Math.Cohomology.Universal.Prop42
import E213.Math.Cohomology.Universal.Prop51
import E213.Math.Cohomology.Universal.Prop52
import E213.Math.Cohomology.Universal.Prop53

/-! Spec-as-code entry point for `E213.Math.Cohomology.Universal`.

  Prop-level Universal δ²=0 lift sequence — a cochain-by-cochain
  ladder lifting the per-pattern δ²=0 result to ∀-quantified form
  at each (n, k) bidegree.

  ## Files

    * `Core`     — Universal-Lens cochain machinery
    * `Prop`     — Prop wrapper for the universal-quantified form
    * `Prop31`   — (3, 1) lift  (`pattern_eq_at`)
    * `Prop41`   — (4, 1) lift
    * `Prop42`   — (4, 2) lift
    * `Prop51`   — (5, 1) lift
    * `Prop52`   — (5, 2) lift
    * `Prop53`   — (5, 3) lift  (final rung at d ≤ 5)
-/
