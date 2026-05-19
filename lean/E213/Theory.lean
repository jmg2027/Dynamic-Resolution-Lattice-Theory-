import E213.Theory.Atomicity
import E213.Theory.CDDouble
import E213.Theory.Raw.API
import E213.Theory.RawCmpIndependence

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
                      Fold, Hom, Levels, Rec, Signed, **Endomorphic**)
                      + auxiliary substrates (**Congruence**,
                      **ParenthesizationDistinct**; 2026-05-18).
                      Endomorphic (slashOrSelf, foldRaw, swapClosed)
                      absorbed from Theory.Closed on 2026-05-14
                      (endomorphic catamorphism + numbering-system
                      isomorphism machinery; previously named
                      FoldRaw, renamed 2026-05-15).
                      Congruence (`Eqv` generic equivalence closure)
                      + ParenthesizationDistinct (no-slash_assoc
                      counter-example) added on the lens-emergence
                      branch.
    * `CDDouble/`   — generic Order-4 Cayley-Dickson double mechanism
    * `RawCmpIndependence.lean` — root file; axiom-independence of
                      the cmp choice (the only Internal-namespace
                      content in Theory ring; Tree machinery lives in
                      `Term/Internal/Tree*` per ARCHITECTURE.md
                      Theory→Term split)

  ## Out (2026-05-14)

    * `Closed/`     — directory removed.  FoldRaw → Endomorphic
                      (`Raw/Endomorphic.lean`); catamorphism output
                      (Nat213/Bool213/RawCut/NumberingSystem) all
                      moved to Lens.
    * `Tower/`      — directory removed.  Three Tower files
                      (NatPairToInt, NatPairToQPos, NatTripleToZ2)
                      all migrated to `Lens.Number.Nat213.Tower`.
-/
