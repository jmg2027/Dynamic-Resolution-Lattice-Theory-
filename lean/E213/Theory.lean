import E213.Theory.Atomicity
import E213.Theory.CDDouble
import E213.Theory.Closed
import E213.Theory.Nat213
import E213.Theory.Raw
import E213.Theory.RawCmpIndependence
import E213.Theory.Tower

/-! Spec-as-code entry point for `E213.Theory`.

  Theory ring (ARCHITECTURE.md 2026-05-12) — the 213 axiom itself:
  `Raw` type + 4-clause definitional commitments (a, b, slash,
  slash_comm).  Plus forced-uniqueness proofs (Atomicity) and the
  structural observables (depth, leaves, fold, swap).  Built on
  Term API (Tree machinery).  Consumed by Lens.

  ## Sub-clusters

    * `Atomicity/`  — forced-uniqueness proofs (Alive,
                      ArityForcing, Five, FiveHelpers,
                      NonDecomposable, PairForcing,
                      PrimitiveSizes)
    * `Raw/`        — public Raw API (Core, Slash, Swap, SwapSlash,
                      Fold, Hom, Levels, Rec, Signed)
    * `Closed/`     — Closed Raw-derived types (Nat213, Bool213,
                      RawCut, NumberingSystem, FoldRaw)
    * `Nat213/`     — standalone inductive Nat213 + bridges
    * `Tower/`      — number-tower constructions on Closed.Nat213
    * `CDDouble/`   — generic Order-4 Cayley-Dickson double mechanism
    * `RawCmpIndependence.lean` — root file; axiom-independence of
                      the cmp choice (the only Internal-namespace
                      content in Theory ring; Tree machinery lives in
                      `Term/Internal/Tree*` per ARCHITECTURE.md
                      Theory→Term split)
-/
