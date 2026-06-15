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

## The bridge — and a correction

**The Kähler/polarization skeleton is genuinely proven (Hodge layer), not forced.**
On `Δ⁴`'s `H¹`, the framework constructs and proves (∅-axiom):
- **symplectic `Q = [[0,1],[−1,0]]`** (antisymmetric, `Qᵀ=−Q`) — the cup pairing,
  the **phase/gauge** half (carries the CP `i`, `ℤ[J]≅ℤ[i]`, δ=90°).
  `HodgeRiemannJ.complex_structure_and_symplectic`, `SignedCup`.
- **positive-definite metric `h = Q·J = I = diag(+1,+1,+1,+1)`** — the
  **real/metric** half (gravity's Riemannian side).
  `HodgeRiemannJ.hodge_riemann_positive`, `SignedCup.hodge_pairing_is_identity`.
- complex structure `J`, `J²=−I`, `JᵀQJ=Q`, `Q·J≻0` — a genuine **polarization**
  (= the Kähler condition).

So gauge = imaginary/symplectic, gravity = real/metric **is really constructed**
(in the Hodge layer), not a label forced on. **But** it is *not wired to the
gravity file*: `GravityShadow.lean`'s `W=|G|²/d` is a real **scalar** (`=d=5`),
its `phase_modulus_separation` is `: True := trivial` (a placeholder), and that
file imports none of `HodgeRiemannJ`/`SignedCup`/`DiscreteGaussBonnet`.  The
skeleton is proven; the gravity label is assigned; **the two are not bolted
together.**

**Correction (an earlier error here):** the `b₁`s do *not* match across the two
pictures.  `DiscreteGaussBonnet`'s `totalCurv = 2−2·b₁` uses the **simple**
`K_{3,2}` (6 edges, `b₁ = 2`); the gauge adjoint `b₁ = NS²−1 = 8` is on the
**multiplicity-2** `K_{3,2}^{(2)}` (12 edges).  Different objects, different
`b₁` (2 vs 8) — so "gravity-curvature = the same `b₁` as the gauge adjoint" is a
**conflation, not a seam**.  Connecting the discrete graph curvature to the Gram
metric would be a forced bridge (the curvature is pure graph combinatorics,
`κ(v)=2−deg(v)`, with no contact with `⟨·|·⟩`).  The honest curvature question
is the curvature *of the proven metric `h`*, which the repo does not compute.

## The deep question (holonomy / Riemannian) — unchanged, honestly open

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

**The natural first brick — DONE (PURE).**  `SignedCup.gram_hermitian_gravity_gauge_split`
assembles the Hermitian `G = h + i·Q` on `Δ⁴`'s `H¹` (`GRe = hPair`, `GIm = cup1`)
and proves the canonical split: **`Re(G)` symmetric positive-definite (`= I`, the
Riemannian/gravity half)** `∧` **`Im(G)` antisymmetric (the symplectic/gauge
half)** — Hermitian-ness *is* exactly this split.  Uses only already-proven
pieces (`hodge_pairing_is_identity` §3 + `cup1_antisymmetric` §2); turns the
asserted "phase/modulus separation automatic from `⟨·|·⟩`"
(`GravityShadow.phase_modulus_separation : True`) into a derived theorem.  No new
physics, no forced map.  *Remaining wiring:* `GravityShadow`'s scalar `W=|G|²/d`
to this `Re(G)=h` (currently the metric lives in the cohomology layer, the scalar
in the physics file — they still don't import each other).

**The second brick — DONE (PURE).**  `Cosmology.MetricHolonomyBridge.metric_J_is_holonomy_S`
identifies the metric's complex structure `J = (0,−1,1,0)` (which builds
`h = Q·J`) with the **elliptic holonomy generator** `Mat2.S = ⟨0,−1,1,0⟩` of the
modular holonomy (`HolonomyLattice`): same 90° matrix, both `² = −I`, and the
loop `holonomy [S,S] = −I` is the first non-trivial deficit.  This **resolves the
phase-vs-modulus / holonomy reconciliation at the generator level**: "gravity =
metric" (current 213) and "gravity = holonomy/deficit" (Regge) are the *same*
object, because the metric's defining `J` IS the holonomy generator `S`.  The
metric is the flat face (`det`-holonomy ≡ 1); the first deficit is the same
matrix's loop `S² = −I`.  No forced map — only the proven `J` and `S` identified.

Harder, genuinely-open second tier (the curvature *field*):
1. The curvature *field* — a connection transporting `h` over a **multi-simplex
   lattice** so curvature varies point-to-point.  The repo has only ONE flat
   `Δ⁴` (`h = I`) and no transporting connection on `H¹`; the holonomy lives on
   the `Mat2` modular monoid, not yet on `H¹`-sections over a glued lattice.
   This is the genuine open substrate (candidate-3 "gluing" has no referent yet).
2. `G_N` (Newton) — not derived; the `M_Pl/v_H = 5²⁵/6` hierarchy is the only
   formalized gravitational number.
3. Extend the `J=S` generator identity to a transport: build the multi-simplex
   lattice and the `H¹`-connection whose holonomy generator is `S`, so the single
   deficit `S²=−I` becomes a curvature field.  (Do NOT import the graph
   `DiscreteGaussBonnet`, which is unconnected — `b₁` differs 2 vs 8.)

Caveat (honest): only the *polarization skeleton* (`Q`, `h=I`, `J`) is proven;
`W`-as-metric, any curvature, `G_N`, and the modulus-vs-holonomy question are
open.  This is a reconnection *opportunity* with a proven skeleton and one
natural assembling theorem — not a closed result.
