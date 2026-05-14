import E213.Theory.Atomicity
import E213.Theory.CDDouble
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
                      Fold, Hom, Levels, Rec, Signed, **FoldRaw**).
                      FoldRaw (slashOrSelf, foldRaw, swapClosed) 는
                      2026-05-14 에 Theory.Closed 에서 흡수
                      (closed-universe machinery 가 Raw API 의 자연
                      확장).  `Closed/` 디렉토리 자체 제거 — 그 안의
                      catamorphism output (Nat213/Bool213/RawCut/
                      NumberingSystem) 은 모두 Lens 으로 이전.
    * `Tower/`      — number-tower constructions on Nat213
                      (NatPairToInt, NatTripleToZ2).
                      NatPairToQPos 은 Lens.Number.Nat213.Tower 로
                      이전 (Peano 의존, 2026-05-14).
    * `CDDouble/`   — generic Order-4 Cayley-Dickson double mechanism
    * `RawCmpIndependence.lean` — root file; axiom-independence of
                      the cmp choice (the only Internal-namespace
                      content in Theory ring; Tree machinery lives in
                      `Term/Internal/Tree*` per ARCHITECTURE.md
                      Theory→Term split)
-/
