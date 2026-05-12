import E213.Theory.Atomicity
import E213.Theory.Raw
import E213.Theory.Tools.CertChecker

/-! Spec-as-code entry point for `E213.Theory`.

  Theory ring (ARCHITECTURE.md 2026-05-12) — the 213 axiom itself:
  `Raw` type + 4-clause definitional commitments (a, b, slash,
  slash_comm).  Plus forced-uniqueness proofs (Atomicity) and the
  structural observables (depth, leaves, fold, swap).  Built on
  Term API (Tree machinery).  Consumed by Lens.

  ## Sub-clusters

    * `Atomicity/`  — forced-uniqueness proofs (Alive,
                      ArityForcing*, Five, FiveHelpers,
                      NonDecomposable, PairForcing,
                      PrimitiveSizes)
    * `Raw/`        — public Raw API (Core, Slash, Swap, SwapSlash,
                      Fold, Hom, Levels, Rec, Signed)
    * `Internal/`   — implementation detail
                      (`RawCmpIndependence` — axiom-independence of
                      the cmp choice).  The earlier Tree machinery
                      (`Tree`, `Tree.cmp` lemmas) lives in
                      `Term/Internal/Tree*` per ARCHITECTURE.md
                      Theory→Term split.

  ## Top-level

    * `Raw.lean`              — Raw cluster re-export shim
    * `Tools/CertChecker`     — certificate-checking utility
-/
