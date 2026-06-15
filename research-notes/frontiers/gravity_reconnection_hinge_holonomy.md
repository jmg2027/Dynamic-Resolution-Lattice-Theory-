# Gravity reconnection — hinge-area (Regge) ↔ current Gram-shadow, via curvature = 2−2b₁

**Status: open frontier (reconnection opportunity).**  Two gravity pictures
exist in the repo, unconnected; the originator's early "gravity = hinge area"
(Regge) research is the math-branch discrete curvature, not yet deployed as
physics gravity.  Now that the SM gauge structure is organized
(`SU(3)×SU(2)×U(1)` from `K_{3,2} ⊂ Δ⁴`, depths from rank exhaustion), the
reconnection is feasible.

## The two pictures (currently unconnected)

1. **Physics-branch gravity = Gram modulus shadow.**
   `Lib/Physics/Cosmology/GravityShadow.lean`: `G_ij = ⟨ψ_i|ψ_j⟩` (complex
   Hermitian); **gauge = phase** of `G` (SU-rotation invariant), **gravity =
   modulus** `W = |G|²/d` (graviton = trace mode, `MasslessParticles`).
   Gravity strength `∝ 1/d`; hierarchy `M_Pl/v_H = d^(d²)/(d+1)`.  Structural
   only — `G_N` (Newton) numerical derivation **not done** ("quantum-gravity
   sub-project").

2. **Math-branch discrete curvature = the Regge/hinge machinery.**
   `Lib/Math/Geometry/GeometrizationConjecture/{DiscreteGaussBonnet,DiscreteRicci}`
   (+ Forman, Ollivier, Bakry–Émery, the A6 FLOW core): vertex curvature
   `κ(v) = 2 − deg(v)`, **total curvature `Σ_v κ(v) = 2χ = 2 − 2·b₁`** on
   `K_{m,n}` (the central object).  Curvature sign ↔ topology, PURE.  This is
   the discrete Regge picture (curvature concentrated on simplicial loci), but
   it lives as pure math, **not deployed as physics gravity.**

## The bridge that already exists

`DiscreteGaussBonnet`: **total curvature `= 2 − 2·b₁`** on `K`.  But `b₁(K) =
NS²−1 = 8` IS the gauge content (`K32Projection`).  So the gravitational
curvature (Regge total) is determined by the same `b₁` that gives the gauge
adjoint — gauge and curvature are two readings of the topology of the *same*
`K ⊂ Δ⁴`.  Hinge language is already in the physics (`Simplex/FoccSpectrum`:
"gauge = hinge k-vertex"; `Simplex/FaceTerms`: "all are cohomology quantities
of `K_{NS,NT}^{(c)} ⊂ Δ⁴`").

## The deep question (holonomy / Riemannian)

In Regge, **curvature = deficit angle = holonomy** of parallel transport around
a hinge (a rotation = a *phase*).  But current 213 puts **gravity in the
modulus, gauge in the phase** — the *opposite* assignment from the standard
"both gravity (Levi-Civita) and gauge are connections, their holonomy is the
field strength."  The tension to resolve:

- **Standard / Regge**: gravity = holonomy = phase (deficit-angle rotation).
- **Current 213**: gravity = modulus shadow; gauge = phase.

Is there a single connection / holonomy group on `K ⊂ Δ⁴` whose phase-part is
the `SU(3)×SU(2)×U(1)` gauge holonomy and whose geometric part is the Regge
deficit (gravity) — i.e. a lattice gauge–gravity unification, with the
phase/modulus split being one Lens reading and the Regge holonomy another?  The
discrete-curvature machinery (math branch) + the gauge cohomology (physics
branch) are the two halves; `curvature = 2−2b₁` is the seam.

## Concrete next steps

1. Deploy `DiscreteGaussBonnet` / `DiscreteRicci` (math) as the physics gravity
   curvature on `Δ⁴` hinges (the 2-faces), re-deriving the Regge "hinge area ×
   deficit angle" Einstein–Hilbert form 213-natively.
2. Relate the Regge deficit (holonomy/phase) to the Gram-shadow modulus `W` —
   are they the same gravity (two Lens readings) or competing?  This is the
   phase-vs-modulus reconciliation.
3. Test whether `curvature = 2−2b₁` upgrades to a genuine gauge–gravity
   identity (gravity's total curvature fixed by the gauge `b₁`), and whether
   the full holonomy group on `K ⊂ Δ⁴` contains both the SM gauge group and the
   geometric (Levi-Civita) part.

Caveat (honest): `G_N` is not derived; the phase/modulus-vs-Regge question is
genuinely open; this is a reconnection *opportunity*, not a closed result.
