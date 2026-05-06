import E213.Math.Cohomology.Cup.Core
import E213.Math.Cohomology.Cup.Leibniz
import E213.Math.Cohomology.Cup.Ring

/-! Spec-as-code entry point for `E213.Math.Cohomology.Cup`.

  Strict cup product on Cochains.

  ## Files

    * `Core`     — `cup p q : Cochain n p → Cochain n q →
                   Cochain n (p+q)`, definition + well-definedness
    * `Leibniz`  — Leibniz rule δ(α ⌣ β) = δα ⌣ β + (-1)^p α ⌣ δβ
    * `Ring`     — H* ring structure induced by `cup`

  See also: `CupAW/` for the Alexander–Whitney variant.
-/
