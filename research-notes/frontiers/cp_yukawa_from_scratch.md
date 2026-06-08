# Frontier — the CP phase from a first-principles Yukawa (honest negative + clarification)

**Status**: OPEN (the specific physical angle); the *maximal-CP* content is closed.
**Domain**: physics (CKM / CP). **Opened**: 2026-06-08.

## What was attempted

The last open item of the CP-phase derivation (`theory/physics/cp_phase.md`): an
**ab-initio Yukawa** — construct the `5̄⊕10` generation Yukawa matrices from 213
structure (down carrying the Hodge complex structure `J=i`, up real), diagonalise,
and have a **specific physical angle** (the right-triangle `α=90°`) emerge,
*without* assuming it.

## The honest negative result

**A generic `J`-carrying Yukawa texture does NOT force `α=90°`.**  Tested
(numerically) several structured down-Yukawa textures with the complex structure
`J` (pure-imaginary couplings) in the apex / nearest-neighbour positions, up real
symmetric:
- pure-imaginary `(1,3)` apex coupling only → `α ≈ 0°` (not 90°);
- Fritzsch nearest-neighbour, pure-imaginary off-diagonals → `α ≈ −38°`;
- single pure-`i` phase in the down mixing → `α ≈ 60°`.

So the physical right-triangle `α = 90°` is **texture-specific**, not a generic
consequence of a `J`-carrying Yukawa.  This matches the literature: `α≈90°` (the
"right unitarity triangle") is obtained by *specific* constructions (Nelson–Barr,
spontaneous CP with a tuned potential) or by *fit*, not from a generic texture
(KM-mechanism agent, Nucl.Phys.B 877 (2013) 752).

## What IS forced (convention-independent) — MAXIMAL CP

The `C₄`/`i` forcing (`CPPhaseC4Forcing`, now premise-closed by `SignedStarFull`)
gives the **phase = the pure imaginary unit `i`** — i.e. **maximal CP**: the
Jarlskog `J` equals its maximum value for the given mixing angles (`sin δ_KM = 1`,
`CPMaximalPhase`).  "Maximal CP" is a convention-independent statement and *is*
forced (the phase is `arg i = 90°` in the KM parametrisation).  The empirical
`δ_KM ≈ 84–90°` (near-maximal) supports it.

## The clarification (and a correction)

Two distinct "`90°`"s were partly conflated and are now separated honestly:
- **`δ_KM = 90°` (maximal CP, KM parametrisation)** — *forced* by `C₄`/`i` (the
  phase is the imaginary unit).  Convention-dependent label, but the physical
  content (maximal `J` / irreducible `i`) is real and forced.
- **`α = 90°` (right unitarity triangle, convention-independent)** — a *separate*,
  stronger, *model-level* claim (`ApexRightTriangle`), **not** forced by the `i`
  alone; it needs a specific texture.  The earlier framing "`α=90°` derived from
  CD `i`" is **over-stated** and should read: `α=90°` is the right-triangle
  *candidate* (empirically `α_obs=92.4°±1.4°`), which *combined with* the derived
  golden modulus `R_u=1/φ²` gives `cos γ=1/φ²`.  What is *forced* is maximal CP,
  not the specific `α`.

## Honest scope now

- **Forced** (Lean PURE): CP existence+uniqueness; the phase ∈ `C₄` (Hodge `⋆`,
  `SignedStarFull`); **maximal CP** (phase = `i`, `CPMaximalPhase`); the `C₄/i =
  signed Hodge ⋆ = ℤ[i] = ℚ(ζ₅)` identity; golden modulus `1/φ²`.
- **Open** (genuinely hard — the literature does it by construction/fit): a
  first-principles Yukawa texture forcing the *specific* physical angle `α=90°`
  (or the apex value); the `~1.5σ` fit.  This is the right-unitarity-triangle /
  Nelson–Barr model-building problem; a generic `J`-texture does **not** suffice.

## Do not

Reverse-engineer a texture to hit `α=90°` (that is fitting, not deriving). The
honest forced content is **maximal CP**; the specific angle is a candidate.

## Anchors
- `theory/physics/cp_phase.md` — the promoted chapter (update its `α=90°` framing
  to "maximal CP forced; `α=90°` candidate").
- `lean/E213/Lib/Physics/Mixing/CPMaximalPhase.lean` — maximal CP (phase = `i`).
- `lean/E213/Lib/Physics/Mixing/ApexRightTriangle.lean` — the `α=90°` candidate + golden modulus.

## ★ Reframing (2026-06-08) — the 213-native Yukawa is NOT a generic texture

The negative above (generic `J`-texture ⇏ `α=90°`) is in the **SM framing**
(arbitrary mass-matrix textures).  But in 213 the Yukawa is **not** a free texture
— it is a *specific* cohomological cup-product object on `H*(Δ⁴)` (the *same*
cup-ring that derives `1/α_em`, `CupRingTrace.lean`).  So the generic-texture
negative **does not apply** to the 213-native Yukawa.

**The genuine 213-native question** (under expert-agent investigation): does the
Yukawa-as-cup-product, carrying the **signed Hodge `⋆` (the Weil operator `J`,
`J²=−1`)**, *force* the CP phase?  Conjecture: a coupling that is a **morphism of
the polarized Hodge structure** (respects the Weil operator `J`) carries `J`'s
phase `arg(i)=90°` — unlike a generic texture (which respects no `J`).  This is
the cohomological (Hodge-theoretic) origin of the Yukawa, where the phase is
*determined* by the Hodge structure, not free.

Two related 213-native anchors:
- **CDI-2** (`catalogs/cross-domain-identifications.md`): `b₁(K₅) = δ_CP =
  SU(5)-adjoint = d²−1 = 24` — a machine-verified 5-way identity linking the
  cohomology (`b₁`) to the CP-sector *count* (24).  The cohomology fixes the CP
  *structure-count*; the signed Hodge `⋆` fixes the *phase* (`i`, 90°).  Together
  the cohomology would determine both.
- The cup-ring functionals `F1..F5` (`CupRingTrace`) are *single numbers* (the
  α_em trace); a **generation-indexed** cup pairing would be the Yukawa *matrix*.

If the Hodge-structure-morphism argument holds, `δ=90°` *is* forced for the
213-native (cohomological) Yukawa — resolving the open item.  Pending agents:
(1) repo cup-ring / Hodge-Riemann pairing pieces; (2) the rigorous Hodge-theory
"does a polarized-Hodge coupling force `δ=π/2`" question.
