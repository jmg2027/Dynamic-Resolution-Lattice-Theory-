# `Lens/Bool213/` — 213-native closed-universe Bool

Raw-encoded Bool: T, F as specific Raw shapes (Method A: T=a, F=b).
Catamorphism `booleanProj := Raw.fold T F and` defines a
Raw-internal projection onto the two-element canonical form
`{T, F}`.  `{T, F}` *is* the Raw image.  Cf. `seed/CLOSED_FORM_SPEC.md`
3-domain table for the ℕ₊ projection comparison.

## Files

  - `Raw.lean`    — Method A canonical encoding + ops
                    (not, and, isBool, booleanProj, boolValue,
                    fixed-point characterisation).
  - `SelfReferenceForms.lean` — Bool-style vs Nat-style self-reference
                    (liar oscillation vs Lambek fixed point).
  - `System.lean` — 메타 (T, F) pattern; arbitrary distinct Raw
                    pair gives valid system; iso preserves
                    not / and (Nat213 의 NumberingSystem과 평행).

## Top-level

  - `Lens/Bool213.lean` aggregator.

## Where to add new files

  - New Bool variant       → `Bool213/<Method>.lean`
  - Boundary mapping       → 직접 `Raw.lean` 에 추가
  - Lens characterisation  → `Bool213/Lenses.lean` (Nat213/Lenses
                              과 평행한 패턴 — 필요 시)

## Discipline

All theorems ∅-axiom (verified via `tools/scan_axioms.py`).

## Distinction from existing Lens Bool files

  - `Lens.Instances.Bool` 등은 Bool *codomain Lens 인스턴스* (AND/OR/
    XOR lens 등).  여기 `Bool213` 은 Bool *type 의 Raw-인코딩 자체*
    (213-native).  서로 다른 의미.
