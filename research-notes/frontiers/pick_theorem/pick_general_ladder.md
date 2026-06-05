# Frontier — Pick's theorem beyond the rectangle (∅-axiom)

**Status**: OPEN.  **Tier**: 1.  A fresh cross-domain conquest compiled onto the
proof-ISA: Pick's theorem (1899) is the **lattice-count ↔ area** bridge — a
*two-readings-agree* identity (the count-fold `I + B/2 − 1` equals the area-fold),
the GRA-universality shape at lattice scale.

## Closed (rung 0)

`Lib/Math/Geometry/PickTheorem.lean` (4 PURE): the **rectangle atom** —
`pick_rectangle`: `2I + B − 2 = 2A` for `[0,w]×[0,h]` with `I=(w−1)(h−1)`,
`B=2w+2h`, `2A=2wh`; a pure `ℤ` ring identity (`ring_intZ`).  The base case from
which the general theorem assembles by additivity.

## Ladder

K1. **Diagonal boundary count** — the open segment `(0,0)–(w,h)` contains exactly
    `gcd(w,h) − 1` lattice points (at `(i·w/g, i·h/g)`, `i=1..g−1`).  The
    number-theory↔geometry engine of every Pick boundary count; uses `gcd213`
    (`Meta/Nat/Gcd213`).
K2. **Right-triangle Pick** — legs `w,h` on the axes: `B = w + h + gcd(w,h)`,
    `I = ((w−1)(h−1) − (gcd(w,h)−1))/2`; `2I + B − 2 = wh = 2A`.  Needs K1 + the
    evenness `(w−1)(h−1) ≡ gcd(w,h)−1 (mod 2)` (the rectangle splits evenly across
    the diagonal except the points on it).
K3. **Additivity** — Pick's value is additive when gluing two polygons along a
    shared edge (the shared boundary points cancel correctly).  The inductive
    engine.
K4. **General simple lattice polygon** — triangulate + induct via K2 + K3.  The
    full theorem.

## ISA reading

Each rung is a **COUNT** (lattice points) bridged to a geometric **READ** (area);
the theorem asserts the two folds are equal.  Rung 0 is the pure-`ring_intZ`
coincidence; K1 brings in `gcd` (number theory); K3 is the additive glue.

## Next action

K1 (the `gcd(w,h) − 1` diagonal count) — self-contained, reuses `gcd213`.
