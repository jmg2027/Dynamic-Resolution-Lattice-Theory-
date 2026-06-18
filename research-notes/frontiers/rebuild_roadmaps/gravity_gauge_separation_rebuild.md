# Gauge / gravity separation rebuild (post-deletion of the `:True` placeholder)

**What was deleted & the bogus mechanism.**  `Lib/Physics/Cosmology/GravityShadow.lean`
(82 lines, deleted in `26c86991e`) asserted a "gauge/gravity separation" with no
content:

```lean
theorem phase_modulus_separation : True := trivial      -- the "separation"
def W_normalization : Nat := d
theorem W_norm_eq_5 : W_normalization = 5 := by decide
-- docstring: "Exact numerical derivation of G_N (Newton constant) is not yet done."
```

The headline `phase_modulus_separation` — the proposition that "gauge = phase of
the Gram, gravity = modulus" — was `True`, proved by `trivial`. The rest was the
scalar `W = |G|²/d = 5` and the atom restatement; the file imported none of the
cohomology machinery (`HodgeRiemannJ`, `SignedCup`) it claimed to be about, so the
"separation" was a label, not a decomposition. `G_N` was openly admitted undone.

**The genuine content.**  A real gauge/gravity split is a **genuine decomposition
of a connection / metric** into its symmetric (Riemannian/metric → gravity) and
antisymmetric (symplectic/phase → gauge) parts, with the field strength being the
**curvature/holonomy** of the connection. "Gravity" then means a real Levi-Civita
connection on a (multi-cell) lattice whose holonomy is the deficit angle (Regge),
ultimately yielding `G_N`; "gauge" means the phase holonomy carrying
`SU(3)×SU(2)×U(1)`.

**The 213-native obstruction.**  The split exists as a *generator-level* identity
but **no curvature field**: there is no `Mat2`-action transporting the metric `h`
over a *multi-simplex* lattice — only one flat `Δ⁴` (`h = I`) exists, and `G_N` is
not derived. Identifying `H¹(Δ⁴)`'s 2-plane with the modular `ℤ²` would be
*forcing* (a shared generator matrix is not a shared field). This is the honest
stopping line. But — unlike the deleted `:True` — the *skeleton* is genuinely
proven, and an existing real frontier already maps the terrain:
- **`research-notes/frontiers/gravity_reconnection_hinge_holonomy.md`** — the
  genuine open frontier. It records two proven bricks and the precise gate.
- **Brick 1 (proven, PURE):** `SignedCup.gram_hermitian_gravity_gauge_split`
  assembles the Hermitian `G = h + i·Q` on `Δ⁴`'s `H¹` and proves the canonical
  split — `Re(G)` symmetric positive-definite (`= I`, the Riemannian/gravity half)
  ∧ `Im(G)` antisymmetric (the symplectic/gauge half). This is the *real*
  theorem the deleted `phase_modulus_separation : True` should have been.
- **Brick 2 (proven, PURE):** `Cosmology/MetricHolonomyBridge.metric_J_is_holonomy_S`
  identifies the metric's complex structure `J = (0,−1,1,0)` (which builds
  `h = Q·J`) entry-for-entry with the elliptic holonomy generator `Mat2.S` of the
  modular `HolonomyLattice`, both `² = −I`, loop `holonomy [S,S] = −I`. So
  "gravity = metric" (current 213) and "gravity = holonomy/deficit" (Regge) are
  the *same* object at the generator level.

**Staged plan (citing genuine seams).**

- **Stage 1 — DONE (the holonomy generator).**  `metric_J_is_holonomy_S`: the
  metric-`J` = holonomy-`S` identity, and `gram_hermitian_gravity_gauge_split`:
  the Hermitian-Gram = metric ⊕ symplectic = gravity ⊕ gauge split. Both PURE,
  both genuine `◑` results (per HANDOFF / the gravity frontier). These *replace*
  the deleted `:True` with proven decompositions.
- **Stage 2 — a `Mat2`-action on `H¹` + an `h`-transport.**  The gate (gravity
  frontier step 1): currently `holonomy` folds `Mat2`-words but never acts on the
  `H¹` 2-plane, and nothing transports `h`. Build a genuine action so the metric
  becomes a *section* over the lattice — without asserting the `H¹ = ℤ²`
  space-identity (that is the forcing line not to cross).
- **Stage 3 — a multi-simplex lattice with a varying metric.**  Glue several `Δ⁴`
  cells so `h` varies cell-to-cell; the deficit angle around a hinge (Regge) is
  then a real curvature, `Σ_v κ(v) = 2χ` connecting to the discrete-curvature
  machinery (`DiscreteGaussBonnet`) *only if* the `b₁`-mismatch (2 vs 8, simple vs
  multiplicity-2 `K_{3,2}`) is resolved — the frontier explicitly warns this is
  currently a conflation, not a seam.
- **Stage 4 — `G_N` from the curvature.**  Only after Stages 2–3 can a Newton
  constant be attempted from the curvature normalisation; today the only
  formalised gravitational number is the hierarchy `M_Pl/v_H = 5²⁵/6`.

**Honest scope.**  Stage 1 is real and proven; Stages 2–4 are *genuinely open
constructions*, not natural next steps. Do NOT type a `G_N` value, do NOT assert
the curvature field exists, and do NOT identify the `H¹` 2-plane with the modular
`ℤ²` (forcing). `G_N`'s absolute value, like H₀, would need an external scale 213
does not supply (no exterior dialer, §5.1). The split (gravity = metric/real, gauge
= phase/symplectic) is constructed; the *field* and `G_N` remain open.

**Cross-references.**
- `research-notes/frontiers/gravity_reconnection_hinge_holonomy.md` (the live frontier — primary)
- `lean/E213/Lib/Physics/Cosmology/MetricHolonomyBridge.lean` (Brick 2, `J = S`)
- `lean/E213/Lib/Math/Cohomology/Cup/SignedCup.lean` (`gram_hermitian_gravity_gauge_split`, Brick 1)
- `lean/E213/Lib/Math/Cohomology/Hodge/SignedStarC4.lean` (`J`, `⋆²=−I`)
- `lean/E213/Lib/Math/Geometry/.../DiscreteGaussBonnet` (Regge curvature; `b₁`-mismatch caveat)
- `seed/AXIOM/05_no_exterior.md` §5.1 (`G_N` scale gap)
