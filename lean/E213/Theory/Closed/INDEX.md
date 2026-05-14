# `Theory/Closed/` — closed Raw-derived types (Theory-side residue)

Closed types built from Raw via the catamorphism `Raw.fold`,
restricted to those whose semantics live in the Theory ring (Raw
algebra itself).  The number-system Closed types migrated to
`Lens.Number.Nat213` on 2026-05-14 because `Raw.fold` + a specific
catamorphism choice = Lens-layer artifact.

  - `Bool213` (closed) — Raw.fold-derived booleans
  - `FoldRaw` — endomorphic fold helpers (`slashOrSelf`,
    `swapClosed`) — Raw → Raw, sits at Theory level

## Files (3)

### Closed Bool213
  - `Bool213.lean`         — `Closed.Bool213` carrier
  - `Bool213System.lean`   — Bool213 system structure

### Raw → Raw helpers
  - `FoldRaw.lean`        — `slashOrSelf` total-slash variant +
                            `swapClosed` (foldRaw 한 줄 표현);
                            endomorphic Raw → Raw fold base

## Moved to `Lens.Number.Nat213/` (2026-05-14)

  - `Nat213.lean`        → `Lens/Number/Nat213/Raw.lean`
  - `Nat213Bridge.lean`  → `Lens/Number/Nat213/Bridge.lean`
  - `NumberingSystem.lean`→ `Lens/Number/Nat213/NumberingSystem.lean`
  - `RawCut.lean`         → `Lens/Number/Nat213/RawCut.lean`

Rationale: 카타모피즘 데이터 캐리어 / numbering / cut 모두 Raw 의
한 가지 *관찰 방식* (Lens) 산물.  Bool213 도 이론상 동일하나 scope C
조사 후 별도 이전.

## Top-level

  - `Theory/Closed.lean` aggregator (imports Bool213 + FoldRaw)

## Discipline

Per ARCHITECTURE.md (2026-05-12) Theory ring: Raw 자체에 대한 구조만
Theory-Closed 에 남김.  Raw 의 catamorphism output 으로 새 number
type 을 정의하는 모듈은 `Lens.Number.<Type>` 로 위치.
