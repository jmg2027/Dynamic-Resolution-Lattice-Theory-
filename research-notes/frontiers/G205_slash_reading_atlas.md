# G205 — The slash-reading atlas: which Lens readings surface the constants

**Status**: open research program (Mingu Jeong, 2026-06-05).
Branch: `claude/geometric-object-relations-yoaI2`.
Below DRLT Validation Standard — exploratory; no precision theorem or
falsifier yet.  Worked atlas + scripts: `research-notes/geometric/`
(`INDEX.md` is the live board for this frontier).

## §1 Starting point

Mingu Jeong's sketch — "an object IS the relation of two distinct objects,
recurse" — is the slash (`02_axiom.md` §2.2).  Rendering it geometrically, the
*reading* chosen at each step (directedness, quotient amount, combining map,
growth rule, readout) controls the shape and which structural invariants
surface.  This is the geometric face of `06_lens_readings.md` §6.

## §2 The core question

**Characterize the readings of the slash that are faithful to the Möbius form
`P = [[2,1],[1,1]]`** (surface `N_S=3, N_T=2, d=5, φ`) **versus the
maximally-symmetric readings that are blind to them.**

Observed (`research-notes/geometric/`): arithmetic-mean betweenness → segment /
Takagi, no constants; free orthogonal reading → `Δ^∞`, dimension but no `P`;
**mediant (Möbius) reading → Stern–Brocot, `P` and `3,2,5,φ` directly.**

**Conjecture (C1), refined by the `M_a` test (`constant_threshold.py`).**
Generalize `P` by one knob — the top-left entry `a` (the count-Lens "two
somethings" of §3.5), glue fixed: `M_a=[[a,1],[1,1]]`, `det = a-1`.

- **Blind ⟺ `det = 0` ⟺ `a = 1`**: `M_1 ≡ 1`, rank-1 collapse — the
  averaging / midpoint degenerate end (the "continuum → point").  This is why
  the earlier midpoint renderings surfaced nothing: they were the `a→1` collapse.
- `det ≠ 0`: a quadratic-irrational fixed point (structured; metallic ratios at
  integer `a` — silver `1+√2` at `a=3`).
- **The 213 values `3,5,φ` sit exactly at `a = 2`** — simultaneously the forced
  count-Lens minimum ("two + binary", §3.2) and the unimodular glue (`det=1`,
  §3.5).  The constants are not tuned: "two somethings" *is* the golden point.

So C1 holds in refined form (blind ⟺ `det=0`; the specific 213 constants ⟺ the
forced `a=2`).  The loop closes back onto §3.2 / §3.5.

## §3 Open knots

- **(K1)** The midpoint ↔ mediant interpolation (denominator `2` ↔ `q+s`):
  locate the threshold where `P` appears — a direct test of C1.
- **(K2)** `K_{3,2}^{(c=2)}` from the construction: split distinguishing into
  state (3) / transition (2) per §6.2, bipartite embedding; connect to the
  closure form `R(N_S,N_T,d,c)·Π(1+κᵢαᵢ^{nᵢ})`.
- **(K3)** `prim-distinct ⟺ linear independence` + the monotone
  `arccos(−1/n) → 90°` climb as ∅-axiom Lean theorems (→ `Lens/` sub-tree;
  see `geometric/dimension_lens.md`).
- **(K4)** Which other `SL(2,ℤ)` generators / de Rham parameters `w` yield
  213-relevant numbers?

## §4 Promotion

Mediant cell already has Lean support (`SternBrocotMarkov`).  Closing (K3) is
the nearest ∅-axiom target.  Atlas stays tier-1 until cells close.
