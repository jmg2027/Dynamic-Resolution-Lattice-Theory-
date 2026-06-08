# Cross-domain insights — the self-reference matrix `M=[[2,1],[1,1]]` as the common root

**Tier 1 (volatile).**  Written at the close of the CKM-apex / Casoratian-sign / Eisenstein
session (branch `claude/ckm-cp-spiral-axis-UTW8U`) against main's CP-phase / three-readouts /
Zolotarev / spiral-axis arcs.  Off-the-top-of-the-head connections; honest split: **buildable**
vs **thematic**.  The unifying object is the Möbius matrix `M = [[2,1],[1,1]]` (the axiom's
algebraic encoding, `seed/AXIOM/03_form.md §3.5`), `M = Q²` with `Q` the Fibonacci matrix.

## 1. The CKM factorises by DISCRIMINANT: modulus on `ℚ(√5)` (+5), phase on `ℚ(i)` (−4) (THEMATIC ★)

The "two-origin CKM" (`A5QuarkApex`: magnitude golden `R_u=1/φ²`, phase `C₄`/`90°`) is, sharpened
by this session, a split by **quadratic field / discriminant**:
- **Modulus** `R_u = (NS−√d)/2 = 1/φ²` lives in the **real**-quadratic golden field `ℚ(√5)`
  (disc `+5`) — the contracting eigenvalue of `M` (`JarlskogApex`, this session's `FibonacciAtomicLock`).
- **Phase** `δ = 90°` lives in the **imaginary**-quadratic Gaussian field `ℚ(i)` (disc `−4`) — the
  Hodge `⋆²=−1`, `ℤ[i]^×=C₄` (main `cp_phase`; this session's `GaussianHodgeBridge`,
  `EisensteinNoComplexStructure` proving disc `−4` selected over disc `−3`).

So the *same* prime `d=5` appears twice: as `+5` (the real golden modulus, `disc M = NS²−4 = d`)
and as the `C₄` at disc `−4` (the phase).  The CKM magnitude/phase factorisation **is** the
real-quadratic / imaginary-quadratic split of the two CM discriminants `{−4,−3}` plus the golden
`+5`.  Buildable seed: state `R_u ∈ ℚ(√5)`, `i ∈ ℚ(√−4)` as the two eigen-fields of the `d=5` object.

## 2. `det = 1` (unimodularity) is the one shared engine (TOOL-LEVEL ★ buildable)

Every arc this session and on main runs through `det`-multiplicativity (`Linalg213.DetMul.det_matMul`):
- `M` (self-reference): `det = 1` ⟹ reciprocal eigenvalues `φ²·(1/φ²)=1` ⟹ the base-normalization
  arrow (one unit leg carries `λ₊`, apex carries `λ₋`).
- Casoratian ladder (branch): `casoratian_det_step` is `det(C·H)=det C·det H`; companion `det=±a₀`.
- `CKMExactUnitarity` (this session): `M·M† = D²·I` — a `det`/unitarity identity over `ℤ[i]`.
- Three-readouts (main): `det(MN)=det M·det N` = `psign_mul` = `legendre_mul`; `det(permMatrix)=psign`.

One `2×2`/`n×n` `det=1` core now serves the **foundational axiom matrix**, **sequence depth**
(Casoratian), **CP physics** (CKM unitarity, Jarlskog), and **number theory** (Legendre/Zolotarev).
Buildable: a single `theory/` note "unimodularity as the shared engine" tying `det M=1` (apex
reciprocity) to `det(AB)=det A det B` (the rest).

## 3. "Modulus = de-signed square" is the same Bool/difference-Lens across rungs (THEMATIC)

This session proved the apex **modulus** is `1/φ²` (two steps, `det Q²=+1`) not `1/φ` (one step,
`det Q=−1`) because a modulus is sign-free (`apex_modulus_is_designed_square`).  The *same*
sign-vs-magnitude (difference-Lens / Bool readout, `CLAUDE.md`) recurs:
- Fibonacci step `det Q = −1` (signed) → square → `det Q² = +1` (magnitude).
- Casoratian multiplier carries a **sign** `altSign(k−1) = psign(shift)` (this branch, `CasoratianPermSign`).
- Cassini `W = ±1` (ℤ-rung, order 2 — the pure sign group).
- The axis rungs ℤ / ℤ[i] / ℤ[ω] each carry a different "sign/root-of-unity group" `{±1}/C₄/C₆`.

So the `det = ±1` dichotomy (SL₂ vs GL₂, the `psign`/Legendre `±1`, the Cassini sign) is one
difference-Lens object read across foundations, analysis, and number theory.

## 4. The companion-matrix structure unifies the Casoratian "fourth readout" with the apex (BUILDABLE)

`M = [[2,1],[1,1]]` is the **companion matrix of `x²−3x+1`** (the apex char poly); the Fibonacci
`Q = [[1,1],[1,0]]` is the companion of `x²−x−1`.  The Casoratian machinery (this branch) is exactly
*companion-determinant* theory: `det_companion`, `cycShift` permutation sign.  So the fourth-readout
framework (companion sign = `psign` of the shift cycle) **applies to `M` itself** — `M`'s order-2
"shift"/reciprocal structure (`det=1`) is a degenerate companion cycle.  Buildable: read the apex
eigenvalue reciprocity `λ₊λ₋=1` through the same `companion_det`/`psign` lens as the Casoratian
ladder, unifying "why `1/φ²`" (apex) with "the companion sign" (depth) on one `2×2` companion.

## 5. `H*(Δ⁴)` is the shared cohomology of BOTH `1/α_em` and the CP phase (THEMATIC, already on main)

Restated for completeness: the signed Hodge `⋆` on the 4-simplex cohomology `H*(Δ⁴)` carries the CP
`i` (this session's `GaussianHodgeBridge` makes it the *same* `C₄` as the spiral-axis floor rotation),
and it is the *same* `Δ⁴` cohomology that derives `1/α_em`.  The order-4 Gaussian rung (phase) and the
`α_em` cohomology share one object; the order-6 Eisenstein rung is excluded (`⋆²=−1` fails, this
session).  Already on main; recorded here as the cohomological leg of the same `d=5` apex.

## Buildable next (ranked)

1. **Unimodularity note** (#2): one `theory/` note tying `det M=1` (apex reciprocity) to
   `det(AB)=det A·det B` across Casoratian / CKM-unitarity / Legendre.  Med.
2. **Companion-cycle reading of the apex** (#4): the apex reciprocal pair through `companion_det`/
   `psign`.  Med.
3. **Two eigen-fields of `d=5`** (#1): `R_u∈ℚ(√5)` (disc +5) vs `i∈ℚ(√−4)` — the modulus/phase split
   as the real/imaginary quadratic decomposition.  Essay seed.
