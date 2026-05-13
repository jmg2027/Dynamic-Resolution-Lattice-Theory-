# `Lens/Cardinality/` — cardinality observables of Raw via Lens

Raw is the substrate; Lens views project Raw → observable space.
Cardinality of Raw and of Lens-image spaces is the canonical
cardinality observable, hence Lens-ring.

Historically these files lived in `Lib/Math/Infinity/` +
`Lens/Algebra/{LensCardinality, CardinalityLB}`.  Consolidated here
2026-05-13 (per LENS_AUDIT §5 quick-win: eliminate Lens→Lib violation
in LensCardinality; Lib/Math/Infinity was structurally Lens-content
mis-housed in Lib).

## Files (9)

  - `Cantor.lean`        — Cantor's theorem, ∅-axiom
                           inhabitant-absence formulation (no
                           Classical, no propext)
  - `Tower.lean`         — Cantor tower (iterated function spaces)
  - `BoolSpace.lean`     — concrete `ℕ → (Raw → Bool)` injection
  - `Countable.lean`     — Raw is at least ℕ-sized
  - `Pair.lean`          — injective pairing `ℕ × ℕ → ℕ`
  - `Godel.lean`         — Σ2: Raw → ℕ injective encoding
  - `Chain.lean`         — chain-space cardinality + R5b reinterpretation
  - `LensCardinality.lean` — Σ4: Lens-image cardinalities
  - `CardinalityLB.lean` — lower bound on Lens kernel space (≥ ℵ₀)

## Path / namespace note

The legacy namespaces `E213.Infinity` and `E213.Theory.Internal` are
preserved across the moved files (used by external consumers).  A
later cleanup pass may rename to `E213.Lens.Cardinality.*` once the
Lens 13→7 sub-cluster consolidation is executed (LENS_AUDIT §4).

## Public surface

The cluster is re-exported via the Lens umbrella `Lens.lean`.  Tier-1
public Lens API (`Lens.API`) does not include these directly — they
are observables / theorems, not core Lens type structure.

## Where to add new cardinality facts

  - About Raw cardinality (lower/upper bounds) → `Countable`,
    `BoolSpace`, `Tower`
  - About Cantor-style absence-of-surjection → `Cantor`, `Tower`
  - About injective Raw ↔ ℕ encoding → `Godel`, `Pair`
  - About Lens-image cardinality (image cardinality of a chosen
    Lens) → `LensCardinality`
  - About Lens-kernel space cardinality (size of the space of
    distinct Lenses) → `CardinalityLB`
