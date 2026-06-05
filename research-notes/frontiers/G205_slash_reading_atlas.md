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

- **(K1) — CLOSED** ∅-axiom (build + `scan_axioms` PURE, 11/0).  The C1 test as
  a theorem: the one-knob family `M_a=[[a,1],[1,1]]`, `det = a−1`, collapse
  (`det 0`) at `a=1`, golden 213 constants (`det 1, trace 3, disc 5`) at the
  forced `a=2`, metallic tower beyond.
  `lean/E213/Lib/Math/Algebra/Mobius213/Px/MetallicThreshold.lean`
  (`detMa_eq`, `detMa_collapse`, `golden_signature`, `metallic_discriminants`,
  `metallic_threshold_master`).
- **(K2) — CLOSED** ∅-axiom (build + `scan_axioms` PURE, 17/0).  The §6.2 graph
  the simplex erased: `K_{3,2}^{(c=2)}` adjacency from the state (3) / transition
  (2) split — bipartite (no within-kind edges), complete across, 12 edges,
  S-degree 4, T-degree 6, handshake 24, and the complete-`K_5`-minus-within
  identity recovering the 6 cross pairs.
  `lean/E213/Lib/Math/Geometry/BipartiteDecomp/K32Adjacency.lean`
  (`no_state_state`, `no_transition_transition`, `cross_complete`, `edge_count`,
  `state_degree`, `transition_degree`, `handshake`, `simplex_minus_within`,
  `k32_adjacency_master`).  (The numerical P-bridge was already in
  `Mobius213K32Bridge`; this adds the adjacency/degree structure.)
- **(K3) — CLOSED** ∅-axiom (build + `scan_axioms` PURE, 11/0).  Both halves
  done: the Möbius / constants half (§2 cites) and the dimension-Lens half —
  `prim-distinct ⟺ linear independence` + approach to orthogonality — now in
  `lean/E213/Lib/Math/Geometry/AngleStructure/SimplexOrthogonality.lean`.  No
  trig, no new reals: `cos = −1/n` is the exact rational inner product of the
  centred vertices, cleared to `Nat` (sign separate).  Cites:
  `cos_mag_is_inv_n` (|cos|=1/n), `partition_dependence` (Σu_i=0),
  `uncentered_orthonormal` (independence ∀ n), `cos_dim_strict_mono` (|cos|→0),
  `simplex_orthogonality_master`.  Sibling of `OrthogonalDoubling` in the
  angle-structure programme.
- **(K4) — half CLOSED.**  The `SL(2,ℤ)`-generator question is answered ∅-axiom
  (build + `scan_axioms` PURE, 14/0): the metallic tower `N_k=[[k,1],[1,0]]`,
  `det=−1 ∀k`, golden the minimal `disc=d=5` rung, `N_1²=P`
  (`Px/MetallicGeneratorTower.lean`).  The de Rham `w`-family is explored
  (`derham_family.py`) but its fractal *dimensions* (Moran / Hausdorff) have no
  `Real213` ∅-axiom shadow — the remaining open edge.

## §4 Promotion

**K1** (C1 threshold, `Px/MetallicThreshold.lean`), **K2** (§6.2 bipartite graph,
`BipartiteDecomp/K32Adjacency.lean`), and **K3** (dimension-Lens orthogonality,
`AngleStructure/SimplexOrthogonality.lean`) are now **closed** ∅-axiom — all
source-of-truth (mediant cell already had `SternBrocotMarkov` / `Mobius213/Px`).
**K4**'s `SL(2,ℤ)`-generator half is closed (`Px/MetallicGeneratorTower.lean`);
its only remaining open is the de Rham fractal *dimension* (needs `Real213`
Hausdorff/Moran machinery, not yet built).  The atlas's structural spine —
K1, K2, K3, and the K4 generator tower — is Lean-verified; what remains is the
fractal-dimension edge alone.

## §5 Deep-research pass (agent-team, goal-directed)

A four-agent deep-research pass (category/domain theory, order/concurrency theory,
number theory/dynamics, repo-first) produced three rigorous characterizations +
one new ∅-axiom theorem.  Capstone: `research-notes/geometric/DEEP_RESEARCH_REPORT.md`.

- **μF ≅ νF coincidence** (`mu_nu_coincidence.md`): static = dynamic **iff the
  reading is algebraic** (every νF element a directed sup of compact elements ⟺
  ω-chain converges at ω ⟺ Cauchy-complete in Barr's depth ultrametric); the gap is
  the Cantor diagonal (`object1_not_surjective`), `2^ℵ₀`.  Dividing line = glue
  (free axis ⟹ coincide; contractive ⟹ gap).
- **Configuration lattice** (`configuration_lattice.md`): the cycle is a
  conflict-free Winskel event structure / Mazurkiewicz trace monoid; confluent
  (Newman), distributive (Birkhoff); **new closed form**
  `I(V,s)=Σ_k C(s,k)2^{Vk}2^{C(k,2)}` = `5,145,72 304 608 555 084 001,…`; covariance
  = schedule-invariance (event structure, **not** a causal set); this IS the DRLT
  lattice.
- **Constants dictionary** (`constants_dictionary.md`): binary slash ⟹ minimal
  quadratic Pisot `φ` (ρ the cubic/global-minimal Pisot); the three φ-frames are
  one `GL(2,ℤ)` datum (Hurwitz ⟺ equidistribution ⟺ quasicrystal); each reading
  carries its renormalization multiplier (φ,ρ algebraic; δ transcendental);
  Bombieri–Taylor is the Pisot⟹quasicrystal mechanism.

**New ∅-axiom theorem:** `BipartiteDecomp/ConfigLatticeCount.lean` (7 PURE) —
`cfgIdeals` with `cycle1=5, cycle2=145, cycle3=72 304 608 555 084 001`; the cycle-3
count was unknown before this pass.

**Next targets (ranked):** (1) mechanize the μF≅νF biconditional / build a
contractive νF; (2) the event-structure/trace layer over Raw + parametric
`cfgIdeals` theorem + link to `Lens/Lattice`; (3) the Lagrange-spectrum link
(`k²+4` already in `MetallicGeneratorTower`) + ρ as a cubic-Pisot object.

## §6 Concrete next target: general `cfgIdeals` theorems (recipe for next session)

The parametric family `cfgIdeals_zero..three` (s=0..3) is closed PURE.  The general
results need `List.range`/`foldr` induction (`List213`); a concrete tractable recipe:

- **`binom_self (n) : binom n n = 1`** — induction on `n`; succ step uses
  `binom_eq_zero_of_lt (n k) : n < k → binom n k = 0` (induction on `n`,
  generalize `k`, case `k = k'+1`).  Both PURE by `Nat` induction (no propext).
- **`Hmono (f L a) : a ≤ List.foldr (fun k acc => acc + f k) a L`** — induction on
  `L` (each step `acc + f k ≥ acc`).  PURE.
- **`cfgIdeals_pos (V s) : 0 < cfgIdeals V s` — CLOSED** ∅-axiom (recursive
  `cfgSum` redefinition; List route abandoned since `range_succ`/`foldr_append`
  are propext-dirty).  Original (now-moot) List recipe: `List.range_succ`
  (`range (s+1) = range s ++ [s]`) + `List.foldr_append` reduce
  `cfgIdeals V s` to `List.foldr g (0 + f s) (range s)`; by `Hmono`,
  `0 + f s ≤ cfgIdeals V s`; and `f s = binom s s * 2^(V*s) * 2^(s*(s-1)/2)
  = 1 * 2^(V*s) * 2^(…) ≥ 1` via `binom_self` + `Nat.one_le_two_pow`/`one_le_pow`.
- Then **`cfgIdeals_dominant (V s) : 2 ^ (V*s) ≤ cfgIdeals V s`** falls out the same
  way (`f s ≥ 2^(V*s)`), the lower bound matching the dominant term.

Verify each with `#print axioms`; the only risk is locating the PURE `List`/`Nat`
core lemmas (`range_succ`, `foldr_append`, `one_le_pow`) — confirm with a scratch
`#print axioms` as was done for `Nat.{zero_add,mul_one,one_mul}` (all PURE here).
