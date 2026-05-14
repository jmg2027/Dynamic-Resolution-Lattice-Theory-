import E213.Theory.Closed.FoldRaw

/-! Spec-as-code entry point for `E213.Theory.Closed`.

  Raw → Raw 의 closed-universe 헬퍼만 잔존.  Catamorphism *output*
  (Nat213, Bool213, RawCut, NumberingSystem) 은 모두 `Lens.{Number,
  Bool213}` 로 이전 (2026-05-14, Raw + 카타모피즘 = Lens 레이어
  산물).

    * `FoldRaw`  — `slashOrSelf` (total slash 변형), `foldRaw`
                   (`Raw.fold (α := Raw)`), `swapClosed`.  Raw
                   알고리즘의 일부, catamorphism *machinery*.
-/
