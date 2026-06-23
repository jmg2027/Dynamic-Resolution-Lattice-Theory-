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
  - `System.lean` — meta (T, F) pattern; arbitrary distinct Raw
                    pair gives valid system; iso preserves
                    not / and (parallel to Nat213's NumberingSystem).

## Top-level

  - `Lens/Bool213.lean` aggregator.

## Where to add new files

  - New Bool variant       → `Bool213/<Method>.lean`
  - Boundary mapping       → add directly to `Raw.lean`
  - Lens characterisation  → `Bool213/Lenses.lean` (pattern parallel to
                              Nat213/Lenses — if needed)

## Discipline

All theorems ∅-axiom (verified via `tools/scan_axioms.py`).

## Distinction from existing Lens Bool files

  - `Lens.Instances.Bool` etc. are Bool *codomain Lens instances* (AND/OR/
    XOR lens, etc.).  Here `Bool213` is the *Raw-encoding of the Bool type
    itself* (213-native).  Different meanings.
