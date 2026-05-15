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
                      Fold, Hom, Levels, Rec, Signed, **Endomorphic**).
                      Endomorphic (slashOrSelf, foldRaw, swapClosed)
                      는 2026-05-14 에 Theory.Closed 에서 흡수
                      (endomorphic catamorphism + numbering-system
                      isomorphism machinery; 구 이름 FoldRaw,
                      2026-05-15 rename).
    * `CDDouble/`   — generic Order-4 Cayley-Dickson double mechanism
    * `RawCmpIndependence.lean` — root file; axiom-independence of
                      the cmp choice (the only Internal-namespace
                      content in Theory ring; Tree machinery lives in
                      `Term/Internal/Tree*` per ARCHITECTURE.md
                      Theory→Term split)

  ## Out (2026-05-14)

    * `Closed/`     — 디렉토리 자체 제거.  FoldRaw → Endomorphic
                      (`Raw/Endomorphic.lean`); catamorphism output
                      (Nat213/Bool213/RawCut/NumberingSystem) 은 모두
                      Lens 으로 이전.
    * `Tower/`      — 디렉토리 자체 제거.  세 Tower 파일 (NatPairToInt,
                      NatPairToQPos, NatTripleToZ2) 모두 `Lens.Number.
                      Nat213.Tower` 로 통합 이전.
-/
