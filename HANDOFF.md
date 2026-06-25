# Session Handoff — Cubic / Eisenstein Reciprocity arc (autonomous)

## Branch
`claude/transport-campaign-progress-dafaoa`.  Full `lake build E213.Lib.Math.Algebra.CayleyDickson`
passes clean.  All new modules ∅-axiom **PURE** except two theorems carrying `propext` only from
Lean-core ℕ↔ℤ cast / divisibility-`decide` bookkeeping (allowed-not-target per
`STRICT_ZERO_AXIOM.md` — propext is Lean-4 kernel base, does **not** falsify).

## Goal of the arc
The roadmap: **ℤ[ω] cubic character `(·/π)₃` → primary primes → the reciprocity law
`(π/π')₃ = (π'/π)₃`**.  This session built the **complete cubic-character theory** and the
**Jacobi-sum substrate**; the reciprocity *law itself* remains (it needs Gauss sums over the
cyclotomic field `ℤ[ζ_p]` — see Frontier).

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

### Jacobi-sum substrate (toward the law)
- `EisensteinFiniteSum` — generic `sumRange` + linearity (`sum_add`, `sum_mul_left`, `sum_congr`).
- `EisensteinCharOrthogonality.geomSum_omega_three_mul` — `Σ_{j<3k} ωʲ = 0` (multiplicative
  character orthogonality, the `N(J)=p` cancellation).
- `EisensteinCubicCharFunction` — the character as a homomorphism `χ̂(i)=ωⁱ`: `chiExp_mul` (hom),
  `chiExp_period` (order 3), `chiExp_value` (μ₃), `chiExp_sum` (`Σχ̂=0`), `chiExp_conj` (`χ̄=χ²`),
  `chiExp_unit` (`|χ|=1`), `chiExp_sum_shift` (translation invariance), `pow_mul`.

## Frontier (recorded in `research-notes/frontiers/carrier_readout_crossdomain.md`)
The **reciprocity law** `(π/π')₃ = (π'/π)₃` itself is the remaining deep capstone.  Its standard proof
needs the **Jacobi sum** `J(χ,χ) = Σ_t χ(t)χ(1−t)` with `N(J)=p`, which routes through **Gauss sums**
`g(χ) = Σ_t χ(t)ζ_p^t` in the **cyclotomic field `ℤ[ζ_p]`** — a large separate construction not yet
started.  Two concrete obstacles: (1) the character *as a function on `𝔽_p`* (with the additive
`t↦1−t`) hits the ZOmega-divisibility-`decide` propext wall and needs the `𝔽_p` additive structure;
(2) `ℤ[ζ_p]` itself must be built.  The character theory it is stated over is **complete and
machine-checked**.

## How to verify
`cd lean && lake build E213.Lib.Math.Algebra.CayleyDickson` ; then from repo root
`python3 tools/scan_axioms.py <module>` per module.
