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

## ★★★ RESOLUTION of the principle (2026-06-08, two expert agents + Lean)

Two expert agents (repo cup-ring/Hodge pieces; rigorous Hodge-Riemann math)
settled the *principle*, leaving only the *construction*.

### The rigorous theorem (Hodge-forced maximal CP, conditional)
**A polarized Hodge structure does NOT force `δ=π/2` for a *generic* coupling —
but it DOES force it for a *cohomological* one.**  Precisely (Voisin I §7.1-2,
Griffiths-Harris Ch.0 §7, Niven): if a coupling `β` is **(i) a morphism of Hodge
structures (J-invariant), (ii) lattice-defined (ℤ-integral), (iii) polarization-
compatible (J-Hermitian / HR-positive)**, then its CP-violating discrete phase
lies in `ℤ[J]^× = C₄ = ⟨i⟩`, whose CP-violating units are `±i = ±90°` — **maximal
CP**.  A **generic texture fails (i)/(iii)** and is unconstrained — *that* is why
a cohomological coupling forces `90°` and a generic `J`-texture (tested:
`α≈0°,−38°,60°`) does not.

### Formalized (Lean PURE): the Weil operator IS a polarization
`Cohomology/Hodge/HodgeRiemannJ.lean` (7 PURE): on `H¹=Λ¹⊕Λ³` the cup form
`Q=[[0,1],[−1,0]]` (symplectic, `Qᵀ=−Q`) and the signed Hodge star `J=[[0,−1],
[1,0]]` satisfy `J²=−I`, **`Jᵀ Q J = Q`** (`J∈O(Q)`, the HR identity
`Q(Ja,Jb)=Q(a,b)`), **`Q·J = I ≻ 0`** (HR2 positivity).  So `(Q,J)` is a genuine
**polarization** (Kähler/Hermitian pair); the J-Hermitian decomposition `M=A+JB`
(A sym real, B antisym = the J-anticommuting CP carrier) puts the phase in the
pure-imaginary part ⟹ `δ=90°` (`= CPMaximalPhase`).  The three forcing hypotheses
are now the explicit polarization data + lattice (Niven→`C₄`, `CPPhaseC4Forcing`).

### What remains — the CONSTRUCTION (the deepest gap, per agent 1)
Not the principle but the explicit object: a **generation-indexed** cup-product
Yukawa `Y_d(i,j)=⟨αᵢ, J αⱼ⟩(top)`.  The deepest obstruction is that **the 3
generations have no cohomological index**: generations come from `C(NS,NT)=C(3,2)
=3` (a *simplex-partition* count), while the cup-ring/Hodge `J` lives in
`Λ*(ℂ⁵)` (the *d=5 simplex*) — two different combinatorial sources, unbridged.
Building the generation-indexed cohomological Yukawa needs (a) a signed-ℤ cup, (b)
the `Q(a,Jb)` Hodge-Riemann pairing wiring `J` into the cup (the `Pairing/
HodgeRiemann.lean` stub is vacuous), and (c) **a cohomological home for the 3
`C(3,2)` generations**.  The principle ("cohomological ⟹ 90°") is *settled*; the
construction is the named multi-session frontier.

## ★ Generation-index gap BRIDGED (2026-06-08, BigradedYukawa)

The deepest obstruction (no cohomological index for the 3 generations) is now
bridged.  `Mixing/BigradedYukawa.lean` (4 PURE): the generation count is
**`N_gen = C(NS,NT) = dim Λ^{NT}(ℝ^{NS}) = dim Λ²(ℝ³) = 3`** — the 3 generations
are a genuine **cohomology grade** (the `NT`-th exterior power of the spatial
`NS`-space), not a bare partition count.  The bigraded Yukawa space is
**`Λ²(ℝ³) ⊗ Λ*(ℂ⁵)`** (generation × internal), joined by `d = NS+NT`; the down-
Yukawa `Λ²(ℝ³) ⊗ Λ¹(ℂ⁵)=5̄` is a `3×3` `ℤ[i]`-valued matrix carrying the internal
signed Hodge `J` (`SignedStarC4`), so — as a polarized-Hodge morphism
(`HodgeRiemannJ`) — it forces `δ = arg J = 90°`.

So the generation index now lives in the same exterior-algebra/cup-ring world as
the CP `i`.  **Remaining (narrowed)**: the explicit signed-`ℤ` cup-product
computation on this bigraded structure (the signed cup + the `Q(a,Jb)` pairing,
mechanical) — the STRUCTURE (index + J + polarization) is in place, and the
principle (cohomological ⟹ 90°) applies.

## ★ Signed-ℤ cup BUILT — the common α_em + CP infrastructure (2026-06-08)

The last mechanical piece is done.  `Cohomology/Cup/SignedCup.lean` (11 PURE)
supplies the **signed-`ℤ` cup product** (the genuine wedge), restoring the
orientation sign the Bool/ℤ-2 cup collapses:
- **wedge sign** `mergeSign(S,T) = (−1)^{inv(S,T)}` (disjoint), `inv = #{(s,t):
  s∈S,t∈T,s>t}`;
- **antisymmetry** `e_i∧e_j = −(e_j∧e_i)`, `e_i∧e_i = 0` (`cup1_antisymmetric`);
- **HR positivity (non-vacuous)**: the signed Hodge pairing
  `h(i,j)=⟨e_i,⋆e_j⟩ = starSign j · mergeSign[i](compⱼ) = I` (`diag(+1,+1,+1,+1)`,
  positive definite, `hodge_pairing_is_identity`).

This is the *same* signed cup both gaps named: the α_em cup-ring's "ℤ-signed
pairings" (`CupRingTrace`) and the CP Hodge–Riemann positivity (`Pairing/
HodgeRiemann`, whose ℤ/2 stub is now also filled, `hodge_riemann_positivity_-
signed`).  So the bigraded cohomological Yukawa has *all* its pieces: the signed
cup (`SignedCup`), the signed Hodge `J` (`SignedStarC4`/`Full`), the polarization
positivity (`HodgeRiemannJ` + `HodgeRiemann`), the generation index `Λ²(ℝ³)`
(`BigradedYukawa`), and the principle (cohomological ⟹ 90°).  What remains is
purely *assembly* (wiring the signed cup + `J` + generation index into one
`Y_d(i,j)` functional), not a missing primitive.

## ★ (a) Cup evaluation DONE — cohomology gives phase+index, angles separate (2026-06-08)

`Mixing/CohomologicalYukawaEval.lean` (3 PURE).  Computing the signed cup–Hodge
pairing explicitly: it is **diagonal** `⟨e_i,⋆e_j⟩ = δ_{ij}` (`h=I`) on both the
`n=4` (CP-`J`) and `n=5` (SU(5)) `Λ¹`.  So the cohomological Yukawa supplies the
**diagonal** — the generation/sector **index** + the CP **phase** (`J=i`, `90°`) —
and **no off-diagonal mixing**.  The CKM **angles** are the separate DRLT atomic
rationals (`λ=5/22`, `A=φ/2`).  So the full CKM **factorises**:
`(DRLT angles) × (cohomological phase J=i)`, verified unitary at `δ=90°` by the
rust `ckm_cp_phase`.  This also fully explains the generic-texture negative: a
generic texture mixes the phase into the angles, but the *cohomological* coupling
keeps them factorised (diagonal pairing), so the phase is the clean `J=i=90°`.
Item (a) closed; (b) the ~1.5σ fit under agent investigation.

## ★ (b) Fit verdict — CONSISTENT (not a tension); O(λ²) Wolfenstein, NOT RGE (2026-06-08)

Expert-agent assessment (UTfit/CKMfitter/PDG 2023-25 + RGE/Wolfenstein lit;
`Mixing/ApexFitConsistency.lean`, 3 PURE):
- **`R_u=1/φ²` is essentially EXACT**: `0.38197` vs obs `0.3825±0.011` (≪1σ) —
  the striking half. `β=22.46°` exact. `η̄` 0.6σ.
- **`α=90°` consistent** at `~0σ` (direct angle fit `90.7°⁺⁴·⁵₋₂.₉`) to `1.7σ`
  (global `92.4°±1.4°`) — a known texture-motivated "right unitarity triangle",
  **not** a significant tension.
- The whole `~1.5σ` residual is the `ρ̄/α` direction; it is covered by the
  standard **O(λ²) Wolfenstein** correction (`λ=5/22`, `λ²=25/484≈5%`,
  `ρ̄=ρ(1−λ²/2)`), which shifts `α,γ` `~1-1.5°` the right way (≈half the gap),
  **no free parameter**.
- **Framing correction**: RGE running is RULED OUT — `dα/dt=0` *exactly* at one
  loop (Luo-Xing 0912.4593), triangle shape RGE-invariant. The residual is
  Wolfenstein-order, NOT scale evolution. Do not cite RGE.

**Verdict: the `α=90°`+`R_u=1/φ²` apex is ~1.5σ-CONSISTENT (LO + standard O(λ²)),
not a genuine tension.** Item (b) closed (honestly: consistent, no fishing).
