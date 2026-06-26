import E213.Lib.Math.Foundations.PatternCatalog.Algebra
import E213.Lib.Math.Foundations.PatternCatalog.Core
import E213.Lib.Math.Foundations.PatternCatalog.CrossAxis
import E213.Lib.Math.Foundations.PatternCatalog.Instance
import E213.Lib.Math.Foundations.PatternCatalog.ParadigmBridge
import E213.Lib.Math.Foundations.PatternCatalog.Span

/-! Spec-as-code entry point for `E213.Lib.Math.Foundations.PatternCatalog`.

  Pattern-catalog formalization — the metaformalization arc
  closure (in research-notes/).  Catalogue of stateable
  patterns and the closure of the catalog under operational
  primitives.

  This sub-cluster groups 5 thematically-related pattern-catalog files;
  the top-level catalog type lives in `PatternCatalog/Core.lean`.

  ## Files

    * `Core`            — pattern-catalog top-level type + ops
    * `Algebra`         — algebraic operations on the catalog
    * `CrossAxis`       — cross-axis pattern interaction
    * `Instance`        — concrete instances of the catalog spec
    * `Span`            — span / closure of the catalog
    * `ParadigmBridge`  — ParadigmDomain ↔ PatternCatalog bridge:
                          ParadigmDomain ≅ Aggregate ∘ Forced on
                          ParadigmWitness (operator word AF)
-/
