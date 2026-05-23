import E213.Lib.Math.PatternCatalog.Algebra
import E213.Lib.Math.PatternCatalog.Core
import E213.Lib.Math.PatternCatalog.CrossAxis
import E213.Lib.Math.PatternCatalog.Instance
import E213.Lib.Math.PatternCatalog.Span

/-! Spec-as-code entry point for `E213.Lib.Math.PatternCatalog`.

  Pattern-catalog formalization — the metaformalization arc
  closure (in research-notes/).  Catalogue of stateable
  patterns and the closure of the catalog under operational
  primitives.

  These were 5 loose files at `Math/` root before M14 Phase B2
  collected them into this sub-cluster.  The original
  `PatternCatalog.lean` (top-level catalog type) renamed to
  `PatternCatalog/Core.lean` per the M11 chapter convention.

  ## Files

    * `Core`       — pattern-catalog top-level type + ops
    * `Algebra`    — algebraic operations on the catalog
    * `CrossAxis`  — cross-axis pattern interaction
    * `Instance`   — concrete instances of the catalog spec
    * `Span`       — span / closure of the catalog
-/
