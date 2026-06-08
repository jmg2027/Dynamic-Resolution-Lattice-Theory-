# The CKM CP phase as one imaginary unit

The CP-violating phase of quark mixing is the **signed Hodge star `⋆` on
`H*(Δ⁴)`** — the order-4 rotation `J = [[0,−1],[1,0]]` with `⋆² = −1`, read
as the generator of `ℤ[i]^× = C₄`.  Its argument is `90°` because that is the
argument of `i`, and `i` is the only root of unity the structure admits.  The
golden ratio is elsewhere — in the mixing *modulus* `R_u = 1/φ²`, not the
phase.

## 213-native answer

A CKM CP phase is not a free angle dialed onto a texture.  It is the
**orientation sign carried by the cohomology of the `(d−1) = 4`-dimensional
simplex `Δ⁴`** at grades `1` and `3`, where the signed Hodge star squares to
`−1` (`Hodge/SignedStarFull`, `starSq_neg_one` for every grade-1 direction;
`Mixing/CPHodgeStructure.starSqParity` for the `k = 1,3` parity).  That star
is `J`, and `J` generates a cyclic group of order exactly 4
(`SignedStarFull`: `J ≠ I`, `J² = −I ≠ I`, `J⁴ = I` ⇒ order `= 4`), i.e.
`C₄ = ℤ[i]^×` (`Hodge/SignedStarC4`: the ring map `elt(a,b) = (a,−b,b,a)`,
`ℤ[J] ≅ ℤ[i]`, `det = a²+b²`).  The phase **is** that generator; its only
non-real powers are `±i`, whose argument is `90°`.

## Derivation

The chain is recorded in `theory/physics/cp_phase.md`; the essay walks it as
one trajectory.

**Existence and uniqueness are counting.**  The number of physical CP phases
in an `N_gen × N_gen` mixing matrix is `(N_gen−1)(N_gen−2)/2`, and
`N_gen = C(NS, NT) = C(3,2) = 3` is the Kobayashi–Maskawa generation count read
off the simplex (`Mixing/CPPhaseCount`: `N_gen = 3 ⇒ ckmAngles = 3`,
`ckmPhases = 1`).  Three generations give exactly one phase — not zero (which
would forbid CP) and not more.  This step is *derived*, with no premise about
the phase's value.

**The value is forced, not fit.**  A discrete CP phase that is a symmetry
eigenvalue has rational cosine (Niven: the only rational-cosine angles are
`0°, 60°, 90°, 120°, 180°`), so it is a root of unity.  A *real* phase
(`J = 0`, `cos δ = ±1`) is excluded the moment CP exists (one physical phase,
nonzero Jarlskog).  Among the Niven-allowed roots of unity the structure
selects `C₄` over `C₆` arithmetically: `d = 5 ≡ 1 (mod 4)` splits in the
Gaussian integers, `5 = (2+i)(2−i) = 2²+1²` (`Icosahedral/CyclotomicFive`),
opening `μ₄ = ⟨i⟩`, while `5` is inert in the Eisenstein integers `ℤ[ω]`,
closing `μ₆ = ⟨−ω⟩`.  So `δ = arg(i) = 90°` (`Mixing/CPPhaseC4Forcing`:
`c4 = [(1,0),(0,1),(−1,0),(0,−1)]`, `delta_ninety_forced`).

**The forcing is cohomological, not textural.**  A *generic* `3×3` complex
mass texture does not give `90°` — diagonalizing an arbitrary Yukawa returns
whatever phase the entries encode.  What forces `90°` is that the 213 coupling
is not generic: it is a **polarized Hodge morphism**, and the Weil operator
`J` of a polarized Hodge structure satisfies three conditions a generic
texture fails — `J² = −I`, `Jᵀ Q J = Q` (isometry of the polarization), and
`h = Q·J = I ≻ 0` (Hodge–Riemann positivity) (`Hodge/HodgeRiemannJ`:
`Q = (0,1,−1,0)`, `hodge_riemann_positivity_signed`; assembled in
`Cohomology/HodgeConjecture/Pairing/HodgeRiemann`).  Under those three the
coupling's phase **must** be the Weil `J`, whose argument is `90°`.  The
positivity `h = I`, `det h = 1` is the same antisymmetric inversion sign the
signed cup product carries (`Cup/SignedCup`: `mergeSign = (−1)^inv`, `cup1`
antisymmetric, `hPair = I`).

**The same `i` is `1/α_em`'s `i`.**  The cohomology `H*(Δ⁴)` whose grade-1,3
star gives the CP phase is the *same* `H*(Δ⁴)` that grades the `1/α_em`
counting — one simplex, one complex structure, two observables.  This is why
the CP phase needs no second postulate: the imaginary unit is already in the
electromagnetic sector's cohomology.

## Dual function

Read as the textbook object, this is the Cabibbo–Kobayashi–Maskawa phase with
its packaging stripped: the Standard Model carries `δ_CKM ≈ 90°` as a measured
input, and the "complex Yukawa coupling" is exactly a Hodge-structure morphism
whose Weil operator is the imaginary unit.  213's reading is sharper in that it
*forbids* the alternatives the textbook leaves open — a golden phase
`δ = π/φ²` is Niven-impossible, a `60°` phase is closed by `5`'s inertness in
`ℤ[ω]`, and a real (CP-conserving) phase is excluded by the generation count.
The classical "free phase" and the 213 "forced root of unity" are the same
quantity; only the second knows it cannot be anything else.

## Cross-frame connections

The imaginary unit appears in four frames and they are one object:

  - **group** — `ℤ[i]^× = C₄`, the Cayley–Dickson doubling at `NT = 2`
    (`SignedStarC4`);
  - **number theory** — the Galois group `Gal(ℚ(ζ₅)/ℚ) ≅ (ℤ/5)^× ≅ C₄`
    carries the phase, while the real subfield `ℚ(√5) = ℚ(φ)` carries the
    golden *modulus* (`CyclotomicFive`, `A5ThreeRepPhase`): one field, phase
    and modulus as Galois group and Gauss period;
  - **cohomology** — the signed Hodge star `⋆` on `H*(Δ⁴)`
    (`SignedStarFull`, `HodgeRiemannJ`);
  - **combinatorial sign** — the inversion parity `(−1)^inv` that the signed
    cup, the permutation sign `det(permMatrix σ) = psign σ`, and (via
    Zolotarev) the Legendre symbol `(a/p)` all read.

The last frame is the bridge to the existing synthesis essay
`the_permutation_under_three_readouts`: the permutation sign, the determinant,
the Legendre symbol, and the Hodge-`⋆` orientation are one antisymmetric
readout, and `d = 5 ≡ 1 (mod 4) ⇒ (−1/5) = +1 ⇒ 5` splits in `ℤ[i] ⇒ μ₄/90°`
is the same Gaussian fact as the quadratic-residue split.  The CP phase is the
fourth readout of the inversion sign.

## Open frontier

Two honest opens, recorded in `research-notes/frontiers/`.

The cohomology fixes the phase and the generation *index* — the diagonal
`h = I` separates into a phase factor and a `Λ²(ℝ³)` generation index — but the
explicit **generation Yukawa cup functional** that produces the mixing
*angles* is a separate DRLT object, not forced by the polarization alone
(`Mixing/CohomologicalYukawaEval`; frontier `cp_yukawa_from_scratch`).  And the
numerical fit is `~1.5σ`-**consistent**, not a tension: `R_u = 1/φ² = 0.382`
matches `0.3825 ± 0.011` essentially exactly, `α = 90°` sits at `~0σ` direct to
`~1.7σ` global, and the residual is `O(λ²)` Wolfenstein with `λ = 5/22`, *not*
renormalization running (`dα/dt = 0` exactly) (`Mixing/ApexFitConsistency`;
frontier `ckm_rho_eta_apex`).  The forced object is the phase; the angle
functional and the last `O(λ²)` of the fit are where the derivation still
points outward.
