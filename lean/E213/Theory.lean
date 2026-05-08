import E213.Theory.Atomicity
import E213.Theory.Raw
import E213.Theory.RawLevels
import E213.Theory.Tools.CertChecker

/-! Spec-as-code entry point for `E213.Theory` (Ring 1).

  Theory layer — the 213 axiom itself: `Raw` type + 4-clause
  definitional commitments (a, b, slash, slash_comm).  Plus the
  forced-uniqueness proofs (Atomicity) and the structural
  observables (depth, leaves, fold, swap).  Consumed by the Lens
  catamorphism algebra (Ring 2).

  ## Sub-clusters

    * `Atomicity/`  — forced-uniqueness proofs (Alive,
                      ArityForcing*, Five, FiveHelpers,
                      NonDecomposable, PairForcing,
                      PrimitiveSizes)
    * `Raw/`        — public Raw API (Core, Slash, Swap, SwapSlash,
                      Fold, Hom, Levels, Rec, Signed)
    * `Internal/`   — implementation detail (Raw/Cmp,
                      CmpIndependence, ComplexityClass);
                      direct import discouraged

  ## Top-level

    * `Raw.lean`              — Raw cluster re-export shim
    * `RawLevels.lean`        — explicit level-≤2 enumeration lists
    * `Tools/CertChecker`     — certificate-checking utility
-/
