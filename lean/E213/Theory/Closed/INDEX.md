# `Theory/Closed/` — closed Raw-derived types

Closed types built from Raw via the catamorphism `Raw.fold`.  These
are *the* canonical Raw-derived types in the Theory ring:

  - `Nat213` (closed) — Raw.fold-derived natural numbers
  - `Bool213` (closed) — Raw.fold-derived booleans
  - `RawCut` — Raw cut for finite computation

Distinct from standalone inductive `Theory.Nat213` (Theory ring
top-level): `Closed/Nat213` IS the Raw-derived definition;
`Theory.Nat213` is a standalone inductive that bridges to it.

## Files (7)

### Closed Nat213
  - `Nat213.lean`        — `Closed.Nat213` Raw-derived def
                            (zero := Raw.a, succ := via fold)
  - `Nat213Bridge.lean`  — bridge to standalone `Theory.Nat213`

### Closed Bool213
  - `Bool213.lean`         — `Closed.Bool213` carrier
  - `Bool213System.lean`   — Bool213 system structure

### Raw cuts + numbering
  - `RawCut.lean`         — Raw cut for finite computation
  - `FoldRaw.lean`        — fold-derived Raw observables
  - `NumberingSystem.lean`— numbering-system structure

## Top-level

  - `Theory/Closed/<ts>` aggregator inside `Theory.lean`

## Where to add new files

  - New Raw-derived type    → `Closed/<Type>.lean`
  - Bridge to standalone    → `<Type>Bridge.lean`
  - Numbering / Raw cut     → `RawCut*` / `NumberingSystem*`

## Discipline

Per ARCHITECTURE.md (2026-05-12) Theory ring: Closed types are
*Raw-derived* and live in the Theory ring; standalone Theory.X
inductive may exist for ergonomics, but Closed.X is the canonical
form.
