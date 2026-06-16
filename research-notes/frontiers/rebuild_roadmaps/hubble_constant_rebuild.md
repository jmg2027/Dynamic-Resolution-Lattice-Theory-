# Hubble constant H₀ rebuild (post-deletion of the `:True` headline)

**What was deleted & the bogus mechanism.**  `Lib/Physics/Cosmology/HubbleConstant.lean`
(43 lines, deleted in `26c86991e`) carried a famous name with no derived value:

```lean
/-- Cosmic dimension constant: H_0 has units 1/time. ... -/
theorem hubble_uses_v_H : True := trivial          -- the "H₀" headline

theorem hubble_atomic : (NS = 3) ∧ (NT = 2) ∧ (d = 5) := by decide
```

The headline `hubble_uses_v_H` was `True`. The only non-vacuous theorem,
`hubble_atomic`, merely restates the atoms `(3,2,5)` — it says nothing about
expansion rate. The docstring itself admitted "0 axioms partial", "structural",
"Currently speculative", and gave a *target* range "67–70" with no derivation.
No `H₀` value, no model, no falsifier.

**The genuine content.**  H₀ is the present **expansion rate** of the universe
(units of inverse time, conventionally km/s/Mpc). Producing it requires a
*cosmological model*: a Friedmann equation `H² = (8πG/3)ρ − k/a² + Λ/3` relating
the rate to the energy content and curvature, plus an *absolute scale* (a length
or time or energy unit) to convert a dimensionless ratio into km/s/Mpc. The
observable "Hubble tension" (CMB ~67.7 vs local ~73) is a discrepancy *between two
measurement routes within such a model* — itself only meaningful once a model is
fixed.

**The 213-native obstruction.**  H₀ is **dimensionful** and 213 has *no exterior
dialer* — no external scale to set the unit of time (`seed/AXIOM/05_no_exterior.md`
§5.1). So an absolute `H₀` in km/s/Mpc is **structurally unreachable from atoms
alone**: it needs an input scale (e.g. `v_H`, or `M_Pl`, plus a Friedmann model)
that 213 does not derive. Pretending otherwise is exactly the deleted file's sin.
What 213 *can* reach is **dimensionless cosmological ratios** — quantities where
the scale cancels — and there is a genuine seam:
- `lean/E213/Lib/Physics/Cosmology/NeffDerivation.lean` — `N_eff` depth integers
  `{1, 2, ∞}` derived (`∅`-axiom, `decide`) from Gram-sector rank exhaustion
  (`C(3,3)=1` saturating `C(3,4)=0`; temporal rank ≤ NT; cross-sector no
  saturation). This is a *real* dimensionless cosmological quantity from counting,
  and it is honest about what is *posited* (the sector→force binding) vs derived
  (the saturation profile).
- adjacent genuine cosmology atoms: `Cosmology/DarkEnergy.lean` (Ω-type ratios),
  `Cosmology/EtaBFalsifier.lean`, `Cosmology/EfoldsFalsifier.lean` — falsifier
  windows on dimensionless quantities.

**Staged plan (citing genuine seams).**

- **Stage 1 — a dimensionless ratio in a falsifier window, NOT a typed H₀.**
  Target the radiation/relativistic d.o.f. count: state `N_eff` from
  `NeffDerivation` as a measurable prediction with an honest window
  (observed `N_eff ≈ 2.99 ± 0.17`), in the same style as `EtaBFalsifier`. The
  deliverable is a `∅`-axiom theorem bracketing a *dimensionless* observable, with
  the sector→force reading flagged as posited (the file already does this).
- **Stage 2 — a second scale-free ratio.**  Attempt an `Ω`-component ratio (e.g.
  `Ω_b/Ω_c` or a `Λ`-related ratio) from the same Gram/atom combinatorics, again
  dimensionless, with a window. Two independent ratios make the cosmology branch
  falsifiable without an absolute scale.
- **Stage 3 — the tension, stated honestly.**  If (and only if) a *ratio of two
  derivation routes* emerges naturally from distinct Lens readings of the same
  structure, state the CMB-vs-local discrepancy as that ratio — never as two typed
  H₀ values. Do not assert "the tension is a 213 signature" without such a ratio.
- **Stage 4 — the scale gap, made explicit (permanent).**  Write down precisely
  *which* external input an absolute H₀ would require (a Friedmann model + one
  scale, e.g. `v_H` in GeV → 1/time via `ℏc`), and that 213 does not supply it.
  This is the honest stopping line, mirroring the gravity frontier's `G_N` caveat.

**Honest scope.**  No theorem may be named/typed as an absolute `H₀`. The
absolute value in km/s/Mpc needs a cosmological model **and** an external scale
that 213 structurally lacks (no exterior dialer); flag this irreducibly. Only
dimensionless ratios (`N_eff`, Ω-ratios) are genuinely reachable from atoms, and
even those carry a *posited* sector→force reading. Prohibited: any "67–70 range",
"speculative", or timeline language.

**Cross-references.**
- `lean/E213/Lib/Physics/Cosmology/NeffDerivation.lean` (genuine `N_eff` seam)
- `lean/E213/Lib/Physics/Cosmology/DarkEnergy.lean`, `EtaBFalsifier.lean`,
  `EfoldsFalsifier.lean` (dimensionless falsifier windows)
- `seed/AXIOM/05_no_exterior.md` §5.1 (no exterior dialer — the scale gap)
- `seed/AXIOM/08_falsifiability.md` §8.4 (0-parameter = structural absence)
- `research-notes/frontiers/rebuild_roadmaps/gravity_gauge_separation_rebuild.md` (the parallel `G_N` scale gap)
