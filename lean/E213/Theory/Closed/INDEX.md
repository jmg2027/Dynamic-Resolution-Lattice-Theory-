# `Theory/Closed/` — Raw → Raw closed-universe helpers (residue)

Raw 자체에 대한 closed-universe 연산만 잔존 (catamorphism *machinery*).
Catamorphism *output* (Nat213, Bool213, RawCut, NumberingSystem) 은
모두 `Lens.{Number, Bool213}` 로 이전 (2026-05-14).

## Files (1)

  - `FoldRaw.lean`  — `slashOrSelf` (total slash 변형, `Raw.slash`
                      의 `x ≠ y` 증명 요구 우회) + `foldRaw`
                      (`Raw.fold` 의 codomain = Raw alias) +
                      `swapClosed` (Raw.swap 의 foldRaw 한 줄
                      표현).

## Moved out (2026-05-14)

  - `Nat213.lean`        → `Lens/Number/Nat213/Raw.lean`
  - `Nat213Bridge.lean`  → `Lens/Number/Nat213/Bridge.lean`
  - `NumberingSystem.lean`→ `Lens/Number/Nat213/NumberingSystem.lean`
  - `RawCut.lean`         → `Lens/Number/Nat213/RawCut.lean`
  - `Bool213.lean`        → `Lens/Bool213/Raw.lean`         (2026-05-14, scope C)
  - `Bool213System.lean`  → `Lens/Bool213/System.lean`      (2026-05-14, scope C)

## Top-level

  - `Theory/Closed.lean` aggregator (FoldRaw 만 import).

## Future

  - 1-file 디렉토리라 `Theory/FoldRaw.lean` 으로 평탄화 후보 (별도
    commit; namespace `E213.Theory.Closed.{slashOrSelf, foldRaw,
    swapClosed}` 호환성 영향 검토 필요).
