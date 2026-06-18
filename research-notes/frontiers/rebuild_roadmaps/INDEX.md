# Rebuild roadmaps — genuine 213-native reconstructions of the deleted programmes

The multi-pass honesty audit (2026-06-16) deleted a large layer of
**stereotype-matching / forcible-map** content: famous theorem/conjecture
names welded to `:= True`, tautologies (`⟨σ,rfl⟩`, `X=X`), hardcoded literals
(`:= 8`, `:= 137`, `93827=93827`), hand-added fudges (`+50`, `+31`), and
value-coincidences sold as structural identities.  Deleting the fakery is not
the same as abandoning the targets.  Each note here is a **roadmap to rebuild
the genuine thing** — on a real object, computing real content, honest about
what the current 213 substrate cannot yet reach.

**Model / tone**: `research-notes/frontiers/genuine_hodge_rebuild.md` — states
the real conjecture, gives a reachable Stage 1 (Lefschetz (1,1) on the abelian
surface `T⁴`, **done**, `Surfaces/AbelianSurfaceHodge.lean`), outlines open
stages, and is explicit the general conjecture stays open as in mathematics.
Every note follows the 6-part structure: deleted-&-why-bogus → genuine content
→ 213-native obstruction → staged plan (on real kept seams) → honest scope →
cross-refs.

## The roadmaps

### Mathematics — conjectures
- `geometrization_rebuild.md` — genuine Geometrization (prime+JSJ, 8 Thurston
  geometries as a real Lie-group enumeration).  Foothold: the rescued
  `DiscreteCurvature/` (real discrete Ricci/Bakry-Émery/surgery).  No 213-native
  3-manifold/π₁/homogeneous-space exists — the conjecture itself is unreachable;
  Stage 1 is an honest graph-surgery decomposition.
- `exotic_r4_akbulut_cork_rebuild.md` — genuine exotic ℝ⁴ / Akbulut cork (smooth
  4-manifolds, Donaldson/Freedman).  Substrate has zero smooth structure; Stage 1
  is only the surviving `Sym3OctetOrbits` Burnside combinatorics, no 4-manifold.
- `linalg213_rank5_compression_rebuild.md` — the OPEN `Linalg213` chiral
  compression "rank ≤ 5" (a live `-- TODO`).  Pins the genuine non-trivial claim
  (constructive Int kernel for `N≥6` + Gram-rank = span-rank + `5 = NS+NT`
  sourcing), generalising the one concrete witness.
- `cross_domain_identification_rebuild.md` — genuine cross-domain **structural
  maps** (a proven intertwiner `H¹(K) ≅ su(3)-adjoint`), not the deleted CDI
  value-coincidences (`6 ≡ 24 ≡ 8`).  Seam: `OctetModule` Sym(3) module.

### Physics — derive-from-atoms (not typed literals)
- `proton_electron_ratio_rebuild.md` — `m_p/m_e ≈ 6π⁵` via the real
  `Real213/ExpLog/PiCut` Wallis cut (π never typed); honest 19 ppm formula ceiling.
- `mass_ratios_rebuild.md` — `m_t/m_c` (the deleted `+50→137`; honest sum
  `87 = NS·(d²+NT²)`), `m_t/m_b ≈ 25·ζ(2)`, `m_b/m_c`, `τ/μ`, `μ/e` — per-ratio
  honest status (several have NO derivation yet).
- `hadron_meson_masses_rebuild.md` — dimensionless `m_p/Λ_QCD = 3·P(x)`;
  absolute MeV masses flagged as needing a scale (not atom-derivable).
- `ionization_energy_rebuild.md` — scale-free hydrogenic `Z²` ratio law; absolute
  `R_∞` flagged as needing `m_e c²`.

### Foundations / cosmology / gravity
- `kolmogorov_description_length_rebuild.md` — a real `size : Raw → Nat` +
  incompressibility lemma relative to `seed/PROOF_ISA.md`; no absolute `K`
  (no canonical universal machine), only relative-to-language.
- `cross_domain_unification_rebuild.md` — a genuine `Lens/Unified` `LensIso` via
  kernel equality (not the deleted `:= True` bundle).
- `hubble_constant_rebuild.md` — dimensionless cosmological ratio in a falsifier
  window; absolute H₀ needs a Friedmann model + external scale 213 lacks.
- `gravity_gauge_separation_rebuild.md` — the genuine gauge/gravity split: the
  two proven `◑` bricks (`gram_hermitian_gravity_gauge_split`,
  `MetricHolonomyBridge` `J=S`) + the live `gravity_reconnection_hinge_holonomy`
  frontier; `G_N` open.
- `cp_phase_ckm_delta_rebuild.md` — δ as a computed Fibonacci-convergent bracket
  (the `+31` fudge / `176=176` deleted); seams `CPPhaseHodgeBridge` (C₄=signed
  Hodge ⋆), `JarlskogApex` (`R_u=1/φ²` candidate).

## The recurring honest ceiling

Three obstructions recur and are stated plainly in the notes, not papered over:
1. **No smooth-manifold / homogeneous-space substrate** — Geometrization,
   exotic ℝ⁴ are research-arcs, not cleanups.
2. **No absolute scale** — masses, H₀, R_∞ have dimensionless ratios derivable
   from atoms but absolute values need an external scale 213 does not supply
   (and, per `05_no_exterior.md`, has no dialer for).
3. **Value-coincidence ≠ structural identity** — a genuine bridge needs a
   proven structure-preserving map, not equal integers reached by `decide`.

These roadmaps are the open side of the research cycle; promote each to a
`theory/` chapter only when its Stage closes ∅-axiom.
