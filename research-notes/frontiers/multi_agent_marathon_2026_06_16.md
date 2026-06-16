# Multi-agent debate marathon — 2026-06-16

A round of continuous multi-agent panels (proposer / skeptic / synthesizer per
frontier) across seven high-value / high-difficulty frontiers, each returning the
sharpest insight + one ∅-axiom buildable brick + the honest wall.  Bricks that
landed PURE this session are listed with their theorem; the cross-domain meta-insight
is recorded at the end.

## Bricks landed (∅-axiom, this session)

| Frontier | Theorem (file) | What it is |
|---|---|---|
| Yang–Mills confinement | `colored_confinement_master` (`Physics/YangMills/ColoredGap.lean`) | SOS certificate `Δ₀²−massGap·Δ₀ = 2(2(f₀+f₁+f₂)−3(f₃+f₄))² + 6(f₃−f₄)²` ⇒ every colored eigenmode has `λ ≥ massGap = 4`. The **spectral face of confinement** (angle 1 closed). |
| Atom-forcing criterion | `subsingleton_iff_collapses` (`Meta/AxisSeparation.lean`) | The one-hot readout collapses ⟺ the atom axis is a subsingleton. The checkable kernel of "faithful ⟺ distinguishing". |
| Metric signature | `lorentz_signature_one_three` (`Physics/Mixing/LorentzSignature.lean`) | Diagonal form `diag(−1,+1,+1,+1)`, signature `(1,3)` via orthogonal basis + `det≠0`, sourced `neg=NT−1`, `pos=NS`. |
| PNT / Chebyshev | `four_pow_le_lcm_mul` (`ChebyshevLower.lean`) | `4ⁿ ≤ (2n+1)·lcm(1..2n)` — `ψ`-lower base sharpened `√2`→`2`. |
| Markov uniqueness | `proper_divisor_of_zhang_modulus_lt_two_c` (`Markov/MarkovUniqueness.lean`) | Every proper divisor of `3c±2` is `< 2c` ⇒ `3c±2` is the terminal parametric family (map cap). |

Plus an honesty correction: the `proton_electron_ratio_rebuild` roadmap's Stage-1
bracket claim was **numerically false** (`6π⁵ ∈ (1835.60, 1839.82)` from `π∈(311/99,22/7)`
pins no consecutive integers); `6π⁵` recorded as numerology, not 213-forced.

## The cross-domain meta-insight: the **no-witness duality**

Two panels — Riemann/PNT and Markov — independently hit the *same shape* of wall, and
naming it once is the marathon's main conceptual yield:

> **A conjecture is ∅-axiom-reachable in 213 exactly when its content has a
> count-Lens (finite / unsigned / local) witness; it is walled exactly when its
> content is a *cancellation* or a *uniformity* with no such witness.**

The two instances are duals of one statement:

- **Riemann Hypothesis** — RH is about *cancellation in a signed sum* (`M(N)=Σμ(n)`,
  the difference-Lens of the prime count).  Its size **is** the zero locations: no
  modulus `M(k)` certifies the exponent `½` without already knowing the zeros.  By
  contrast `π`, `ψ`, `lcm` are **unsigned monotone counts** with elementary two-sided
  estimates — so Chebyshev (both halves), the density `π(N)/N→0`, and the `√2→2`
  sharpening are all ∅-axiom.  PNT's "constant = 1" = the computable bracket narrowing
  to `{1}`; collapsing it needs the Erdős–Selberg bilinear step, which has **no
  ∅-axiom shadow**.  Diagnosis: **signed-cancellation has no count-Lens witness.**

- **Markov / Frobenius** — the uniqueness kernel is realizability of a `√(−1)`-suborbit
  of discriminant `9c²−4`.  The distinguishing data provably *leaves `c`* at every
  Vieta descent step (the modulus strictly shrinks), so no fixed-`c` finite signature
  carries it.  Every closed family (`pᵏ`, `2pᵏ`, `3c±2`) is **local in `c`**; the
  `3c±2` lever is now provably the last of its kind (the strip-reframe cap).  Diagnosis:
  **the uniform residue has no local witness.**

These are the same wall read two ways: *signed-cancellation* (RH) and *uniformity over
an unbounded descent* (Markov) are each the negation of a count-Lens / local-finite
witness.  This sits beside the CLAUDE.md "Limit/infinity deified" failure-mode and the
`residue_shape_doctrine`: in 213 a horizon constant is reachable **as a narrowing
computable bracket** precisely when an unsigned monotone count underlies it — and the
genuine open conjectures are exactly those whose content is the *absence* of such a
witness (signed cancellation, or a residue uniform over an unbounded orbit).  Pointing
at that residue **is** the conjecture (Frobenius 1913 / the zero-free region), not a
bounded step — the terminal-localization pattern, now seen to be a general phenomenon.

## Wave 2 — bricks landed (∅-axiom)

| Frontier | Theorem (file) | What it is |
|---|---|---|
| Hodge conjecture (T⁴) | `neron_severi_T4` (`Cohomology/Surfaces/AbelianSurfaceHodge.lean`) | The biconditional `IsHodge11 F ↔ IsAlgebraic F` (`NS(T⁴)=H^{1,1}∩H²`, the full Lefschetz (1,1) for `T⁴`) + rank-`4` ℤ-independent generator basis (`nsComb_injective`) + the genuine gap `H^{1,1}⊊H²`. ∅-axiom-decidable because `J` is a fixed *rational* operator. |
| Metric signature wiring | `time_axis_is_order2_via_NT` (`Physics/Mixing/LorentzSignature.lean`) | The negative axis is canonically the `NT`-sourced order-2 (`i`) axis — count `NT−1`, tied to `NT²=4` and the `Λ¹ ⋆²=−1` by shared `NT` source. |

Plus an honesty fix: `gravity_reconnection_hinge_holonomy.md` cited the **deleted**
`GravityShadow.lean` as a live target; corrected, with the panel's verdict that
"gravity = real part" is a relabeling (the Hermitian split is content-free) and the
standing walls (no `G_N`/scale, blocked `h`-curvature, the `b₁=2` vs `b₁=8` forbidden
bridge) recorded.

Wave-2 walls confirmed: general Hodge (continuous `J` / `(2,2)`-torsion / transcendence
— uncrossable by finite `decide`); the strong "the `−` axis MUST be the `⋆²=−1` carrier"
(⋆² is uniform `(4,0)` on `Λ¹` — no asymmetry to single out one axis).

## Honest walls recorded (not reached this session)

- **YM confinement angle 2** (Wilson-loop area law): no embedding on the abstract
  `K_{3,2}` ⇒ no enclosed "area", no absolute string tension to state; the existing
  holonomy machinery proves the ℕ⁺ sector loop-free (no exponential-in-loop decay there).
- **ζ(3) numerator integrality**: the H₃-term and kernel-term *integrality* are
  reachable (pure divisibility via `cube_dvd_lcm_cube` / `heart_lcm`), but the kernel
  *recurrence* has **no clean WZ certificate** (the harmonic factor leaves the
  proper-hypergeometric class) — a certifiability wall, multi-session by hand.
- **m_p/m_e**: `6π⁵` is a ~19 ppm coincidence; pinning it needs a fast (Machin/arctan)
  π cut that does not exist, and even then certifies a coincidence, not a derivation.
- **RH**: no ∅-axiom shadow at all (the signed-cancellation wall above).
