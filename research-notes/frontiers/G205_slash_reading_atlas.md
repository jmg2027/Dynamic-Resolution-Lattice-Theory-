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

**Status — already closed ∅-axiom in Lean (repo-first; build + `scan_axioms`
verified PURE).**  The geometric C1 exploration independently re-derived the
closed `Mobius213/Px` sub-tree (29 files, promoted to
`theory/math/algebra/mobius213_p_orbit_closure.md`):

- general det in terms of the knob — `Mobius213OneAsGlue.mobius_det_eq_ns_minus_nt`
  (`det = N_S − N_T`); `a=2` glue — `one_is_det`, `mobius_det_is_unit`,
  `Px.CassiniUniversal.cassini_universal` (`det = 1 ∀n`).
- the collapse end (`det = 0`, `N_S = N_T`) — `Mobius213K33Bridge.k33_NS_minus_NT_eq_zero`.
- the lock onto the non-degenerate `(2,3,5)` (vs the degenerate `(1,1,2)` =
  the `a=1` end) — `Px.FibonacciAtomicLock.fibonacci_atomic_lock_master`,
  `atomic_signature_eq_fibonacci`.
- char poly `x² − det·x − det` (the knob as a parameter) —
  `Px.OpenSpeciesClosure`.

What the geometric exploration *adds* is only narrative: the continuous knob `a`
presenting collapse (`a=1`) and golden (`a=2`) as the two ends of **one dial**
(betweenness ↔ mediant).  That is a synthesis for the atlas / a future essay,
not a new theorem.

## §3 Open knots

- **(K1)** The midpoint ↔ mediant interpolation (denominator `2` ↔ `q+s`):
  locate the threshold where `P` appears — a direct test of C1.
- **(K2)** `K_{3,2}^{(c=2)}` from the construction: split distinguishing into
  state (3) / transition (2) per §6.2, bipartite embedding; connect to the
  closure form `R(N_S,N_T,d,c)·Π(1+κᵢαᵢ^{nᵢ})`.
- **(K3)** The Möbius / constants half is **closed** (see §2 status, cites).
  Still open: `prim-distinct ⟺ linear independence` + the approach to
  orthogonality.  **Not trig, not blocked by reals** (correction): `cos = −1/n`
  is the exact rational inner product of the centered vertices
  (`⟨u_i,u_j⟩ = δ_ij − 1/(n+1)`), so the target is a rational-Gram + rational
  limit `−1/n → 0` on the existing `Real213` (Cut-based, Cauchy; cf.
  `PhiConvergence`, `GeometricThreshold`) — counting / linear algebra, a clean
  next target.  See `geometric/dimension_lens.md`.
- **(K4)** Which other `SL(2,ℤ)` generators / de Rham parameters `w` yield
  213-relevant numbers?

## §4 Promotion

Mediant cell already has Lean support (`SternBrocotMarkov`).  Closing (K3) is
the nearest ∅-axiom target.  Atlas stays tier-1 until cells close.
