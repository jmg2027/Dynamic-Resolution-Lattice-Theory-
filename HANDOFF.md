# Session Handoff — Cubic / Eisenstein Reciprocity arc (autonomous)

## Branch
`claude/transport-campaign-progress-dafaoa`.  Full `lake build E213.Lib.Math.Algebra.CayleyDickson`
passes clean.  All Phase-A modules (the character on `𝔽_p` + Jacobi sum) are ∅-axiom **PURE**.  A few
older character-theory capstones carry `propext` only from Lean-core ℕ↔ℤ cast / divisibility-`decide`
bookkeeping (allowed-not-target per `STRICT_ZERO_AXIOM.md` — propext is Lean-4 kernel base, does
**not** falsify).

## Goal of the arc
The roadmap: **ℤ[ω] cubic character `(·/π)₃` → primary primes → the reciprocity law
`(π/π')₃ = (π'/π)₃`**.  Prior sessions built the complete cubic-character theory; **this session built
the character as a genuine multiplicative `μ₃`-valued function on `𝔽_p` (`χ_ω`) and the Jacobi sum
`J(χ,χ)` as a concrete `ℤ[ω]` element** (Phase A1+A2 of the roadmap).  Next: `N(J)=p` (Phase A3) — see
Frontier.

## What is built (in `lean/E213/Lib/Math/Algebra/CayleyDickson/Integer/`, + `ModArith/CubicResidue`)

### The cubic character `(·/d)₃ = α^m`  (`m=(p−1)/3`, `d` a norm-`p` Eisenstein prime, `p≡1 mod 3`)
- **Value group μ₃** — `CubeRootsOfUnity` (`x³=1 ⟺ x∈{1,ω,ω²}`); `EisensteinCubicCharValue`
  (`cubic_factor` `y³−1=(y−1)(y−ω)(y−ω²)`, `cube_one_value`: `y³≡1 ⟹ y≡1∨ω∨ω²`).
- **Cubes-to-one + multiplicative** — `EisensteinCubicChar`: `char_cubes_to_one`, `char_mul`
  (`χ(αβ)=χ(α)χ(β)`), `pow_mul_distrib`.
- **`d` prime / `ℤ[ω]/(d)` integral domain** — `EisensteinPrime`: `norm_prime_euclid`
  (`π∣αβ ⟹ π∣α ∨ π∣β`, via the Euclidean-gcd dichotomy — no excluded middle),
  `residue_no_zero_divisors`.  All PURE.
- **Well-defined as a μ₃-valued function** — `EisensteinCubicCharWelldef`: `root_unique` (the three
  roots distinct mod `d` for `p>3`, via norm-3 differences), `char_value_unique`.
- **Detects cubic residues both ways (Euler criterion)** —
  `cubic_residue_char_one` (cube ⟹ χ=1) + `EisensteinCubicEuler.char_one_implies_cube` (χ=1 ⟹ cube),
  with `int_dvd_pow_sub_pow` (power congruence, PURE) and `cube_lift`.
- **Rational weld (computable symbol)** — `EisensteinCubicChar.char_eq_rational_pow` (`χ(α)≡r^m`),
  `EisensteinCubicWeld.char_one_iff_rational` (`χ(α)=1 ⟺ p∣(r^m−1)`, both directions PURE);
  `ModArith/CubicResidue.pow_m_one_iff_cube` (rational cubic Euler criterion).
- **Supplementary laws** — `EisensteinCubicCharOmega.char_omega_value` (`(ω/d)₃=ω^m`),
  `EisensteinCubicCharConj.char_conj` (`(ᾱ/d)₃=conj(α/d)₃`).

### Primary primes (rung 4)
- `EisensteinPrimary.exists_unique_primary`: for `π` coprime to 3, exactly one of the six unit
  multiples is `≡ 2 (mod 3)`.  7 helpers PURE; capstone carries `propext` (divisibility-`decide`).

### Jacobi-sum substrate (exponent-side, prior)
- `EisensteinFiniteSum` — generic `sumRange` + linearity (`sum_add`, `sum_mul_left`, `sum_congr`).
- `EisensteinCharOrthogonality.geomSum_omega_three_mul` — `Σ_{j<3k} ωʲ = 0`.
- `EisensteinCubicCharFunction` — the character as a homomorphism `χ̂(i)=ωⁱ` (`chiExp_*`).

### Phase A — the cubic character on `𝔽_p` + the Jacobi sum  (this session, all PURE)
Roadmap `research-notes/frontiers/higher_reciprocity_roadmap.md`.  **A1 + A2 COMPLETE.**
- **A1 — the character as a function on `𝔽_p`** (`χ_ω : ℕ → ℤ[ω]`, `μ₃`-valued, multiplicative):
  - `ModArith/CubicCharFp` — rational `χ(t)=t^m%p`: `cubicChar_cube_one` (`χ³≡1`), `cubicChar_mul`,
    `cubicChar_unit`, `cubicChar_one_iff_cube`, `cubicChar_trichotomy` (`χ∈{1,x,x²}`), `cubicChar_mod`.
  - `ModArith/CubeRootsUnityModP` — `cube_root_trichotomy` (`y³≡1 mod p ⟹ y∈{1,x,x²}`, the field
    fact via cubic factorisation + `int_dvd_prime_mul`); pure bridges `dvd_sub_to_mod_eq`,
    `int_dvd_prime_mul`.
  - `Integer/EisensteinResidueFieldCubeRoots` — lift to `ℤ[ω]`: `cube_roots_rational`
    (`{1,ω,ω²}≡{1,x,x²} mod d`), `ofInt_natMod_modEq` (`%p` invisible mod `d`),
    `natMod_value_omega_power`.
  - `Integer/EisensteinCubicCharFp` — computable `chiOmega`: `chiOmega_value`/`chiOmega_unit_value`
    (`μ₃`), `chiOmega_lift` (`ofInt↑χ(t)≡χ_ω(t) mod d`), `chiOmega_mul_conj` (`|χ|=1`).
  - `Integer/EisensteinCubicCharFpMul` — **`chiOmega_mul`** (`χ_ω(s)·χ_ω(t)=χ_ω(st)`, the keystone),
    `mu3_mul_closed`, `mu3_inj` (`root_unique`), `mu3_sum_zero` (`1+ω+ω²=0`).
- **A2 — the Jacobi sum** `Integer/EisensteinJacobiSum`: `jacobiSum = Σ_{t<p} χ_ω(t)·χ_ω((1+(p−t))%p)`;
  `chiOmega_zero_of_dvd`, boundary terms vanish (`jacobi_term_zero/one`).

## Frontier — Phase A3 (`N(J)=J·J̄=p`) and the law
`N(J)=p` is the current frontier.  The character algebra is in hand (`chiOmega_mul`, `mu3_sum_zero`,
`chiOmega_mul_conj`).  **Two concrete gaps** (see roadmap A3):
  1. **`Σ_{t<p} χ_ω(t) = 0`** needs a **`sumRange` permutation-reindexing** lemma under the
     unit-permutation `t↦(a·t)%p` — no such infra in the repo yet; this is the next thing to build.
  2. **Endgame cancellation** `(1−χ_ω(a))·S=0 ∧ χ_ω(a)≠1 ⟹ S=0` (`ZOmegaDomain.no_zero_div`;
     ZOmega right-distributivity via `ext`+`ring_intZ` since `add_mul` is private).
Then `J·J̄=p` by the translation-invariant double sum.  The reciprocity **law** `(π/π')₃=(π'/π)₃`
follows from `J=π` (A4) + the transfer (whether `ℤ[ζ_p]`/Gauss sums are needed — decide on arrival).

## How to verify
`cd lean && lake build E213.Lib.Math.Algebra.CayleyDickson` ; then from repo root
`python3 tools/scan_axioms.py <module>` per module.
