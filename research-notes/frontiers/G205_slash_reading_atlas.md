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

**Conjecture (C1).** A combining map surfaces `P` iff it preserves the
off-diagonal glue (`det = 1`, the `SL(2,ℤ)` / non-symmetric structure);
det-collapsing symmetric averaging is blind.

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
