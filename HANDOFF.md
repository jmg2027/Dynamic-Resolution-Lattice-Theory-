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

### Phase A3 — character orthogonality (this session, all PURE)
- **`Integer/EisensteinScaleCancel`** — `scale_fixed_eq_zero` (`w·S=S, w≠1 ⟹ S=0`, `ℤ[ω]` domain +
  `ext`/`ring_intZ` distributivity `sub_mul_zomega`, `eq_of_sub_eq_zero`).
- **`Integer/EisensteinCharSumZero`** — **`chiListSum_totatives_zero`: `Σ_t χ_ω(t)=0` UNCONDITIONAL**
  for prime `p≡1 mod 3`, `p>3`.  `chiListSum` (`ℤ[ω]` list-sum), `chiListSum_lperm` (perm-invariant via
  `LPerm`+`add_left_comm`), `chiListSum_map_factor` (`Σχ_ω(a·t)=χ_ω(a)·Σχ_ω` via `chiOmega_mul`),
  `chiListSum_scale_zero`.  Permutation from `EulerTheorem.lperm_image`; non-residue = primitive root
  (`chiOmega_ne_one` + `cube_pow_iff_three_dvd_exp`, `g¹` a cube ⟺ `3∣1`, false).

### Phase A3 — toward `N(J)=p` (this session, all PURE)
- **`Integer/EisensteinListSum`** — generic `listSum f L` (ℤ[ω] list sum) + toolkit: `listSum_lperm`
  (perm-invariant), `listSum_append`, `listSum_add`/`mul_left`/`congr` (linearity), `listSum_map`
  (reindex), **`listSum_mul_distrib`** (`(Σf)(Σg)=Σ_s Σ_t f s·g t`, the double-sum engine).
- **`Integer/EisensteinJacobiNorm`** — `jacobiList = Σ_{a<p} χ_ω(a)·χ_ω((1−a)%p)`; `jacobiList_conj`
  (`conj J = Σ χ̄_ω·χ̄_ω`, via `conj_listSum` homomorphism); **`jacobiList_norm_double`**
  (`J·J̄ = Σ_a Σ_b (χ_ω(a)χ_ω(1−a))(χ̄_ω(b)χ̄_ω(1−b))`).
- **`Integer/EisensteinJacobiReindex`** — **`chiOmega_reindex`** (`χ_ω((b·c)%p)·conj χ_ω(b)=χ_ω(c)`,
  the per-term `a=b·c` simplification) + `chiOmega_ne_zero`.

### Phase A3 — the `N(J)=p` reduction machinery (this session, all PURE)
- **`Integer/EisensteinJacobiReduce`** — the multiplicative reindex engine: `listSum_reindex_mul`
  (`Σ_{s∈tot} G(s)=Σ_{s∈tot} G((a·s)%p)`, `lperm_image`), `chiOmega_reindex_conj`
  (`χ_ω(a)·χ̄_ω((a·s)%p)=χ̄_ω(s)`), `rearr4`, `jacobi_inner_term`, **`jacobi_inner_reduce`**
  (inner `b`-sum → `Σ_s χ_ω(1−a)·χ̄_ω(s)·χ̄_ω((1−as)%p)`).

## Frontier — `N(J)=p` needs ADDITIVE characters (route correction) + the law
**KEY FINDING (verified on paper, roadmap A3 step 5):** the pure multiplicative `ℤ[ω]`-internal route
is **CIRCULAR** — `jacobi_inner_reduce` gives `J·J̄=Σ_a χ_ω(1−a)·T(a)`, `T(a)=Σ_s χ̄_ω(s)χ̄_ω((1−as)%p)`,
but `s'=as` makes `T(a)=χ_ω(a)·J̄`, so `J·J̄=J·J̄` (tautology).  `|J|²=p` genuinely needs the **additive
character** (`|g(χ)|²=p` via additive orthogonality `Σ_t ζ^{at}=0`, `p∤a`).  **The reindex machinery
above is still valid infra** (Gauss sums are `listSum`s too), just insufficient alone.

**REVISED next sub-project — route (b), Gauss sums in the FREE group ring** (no quotient ring; the
`e_1`-coefficient extraction replaces it — see roadmap A3 step 5):
  - **`Integer/EisensteinGroupRing` DONE (carrier foundation)** — the free group ring `R[C_p]`
    (`R=ℤ[ω]`, elements = coefficient functions `Nat→ℤ[ω]` mod `p`, `ζ^i=e_i`): `conv` (convolution),
    `conv_add_right`, `conv_scalar_left` (bilinearity).  Discipline: **coefficient equations only**
    (no element equality — `funext` is `Quot`-backed).
  - **`Integer/EisensteinGaussSum` DONE (defs + diagonal):** `gauss := chiOmega`,
    `gaussConj k := conj χ_ω((p−k)%p)`; `conv_diag_index` (`k=0` double-`mod` collapse, pure
    `sub_sub_self_pure`); **`gauss_conj_zero`: `(g⋆ḡ)(0) = ↑(p−1)`** (the `e_0`-coefficient, via
    `diag_count` counting the `p−1` units).
  - **Reindex toolkit for the off-diagonal — DONE this session:**
    - `Combinatorics/RangeList` — pure `rangeList [0,n)` + `mem_rangeList`/`nodup_rangeList`
      (Lean-core `List.range` lemmas are `Classical`-dirty).
    - `Integer/EisensteinRangeSum` — `sumRange_eq_listSum` (bridge `conv` sums to `listSum` so they
      reindex by `[0,p)`-permutations), `rangeList_mul_lperm` (`i↦(a·i)%p` permutes `[0,p)`),
      `rangeList_add_lperm` (`i↦(i+c)%p` permutes `[0,p)`).  The mult+add permutation toolkit.
  - **`Integer/EisensteinGaussOffDiag` DONE (index + reformulation):** `conv_offdiag_index`
    (`(p−(k+p−i)%p)%p = (i+p−k)%p`, pure ℕ arithmetic via 4 sub-identities + `sub_pos_pure`);
    **`gauss_offdiag_sum`: `(g⋆ḡ)(k) = Σ_{i<p} χ_ω(i)·χ̄_ω((i+p−k)%p)`** for `k<p`.
  - `chiOmega_mod` (`EisensteinCubicCharFp`): `χ_ω(a%p)=χ_ω(a)` — the index-bookkeeping helper.
  - **`Integer/EisensteinInvPerm` DONE** — `totativeList_inv_lperm`: inversion `t↦(aInv t p)%p` permutes
    `totativeList p` (involution `t⁻¹⁻¹=t`, via `cancel_unit`).  **The reindex toolkit is now COMPLETE:
    mult (`lperm_image`/`rangeList_mul_lperm`) + additive (`rangeList_add_lperm`) + inversion (this).**
  - **`Integer/EisensteinScaleCancel`** (extended): `mul_sub_zomega`, `mul_left_cancel_zomega`
    (ℤ[ω] left cancellation).  **`Integer/EisensteinCharDiv`**: **`chiOmega_div`**
    (`χ_ω(b)·χ̄_ω(c)=χ_ω((b·aInv c p)%p)`, the per-term ratio identity), `chiOmega_one`, `aInv_mod_pos`.
  - **ALL foundational building blocks for the off-diagonal `−1` are now in place**
    (permutations mult/add/inv, cancellation, the division identity).  **Remaining = ASSEMBLY of the
    sum manipulations:**
    1. **mult-reindex assembly** `i=(k·u)%p` ⟹ `(g⋆ḡ)(k) = C := Σ_u χ_ω(u)·χ̄_ω((u−1)%p)` (`k`-indep);
       `sumRange_eq_listSum` + `rangeList_mul_lperm` + `listSum_lperm`/`_map`/`_congr` + per-term
       (`chiOmega_mul`/`chiOmega_div`); needs index helper `((k·u)%p+p−k)%p = (k·(u−1))%p`.
    2. **`C = −1` assembly** — `u↦u−1` shift + `j↦j⁻¹` inversion (`totativeList_inv_lperm`) + `z=1+w`
       shift + `chiOmega_div` per-term ⟹ `Σ_{z≠1}χ_ω(z)=−1` (`chiListSum_totatives_zero`).
    3. `g(χ)² = J·g(χ²)` coefficient identity (convolution = `listSum_mul_distrib`-style).
    4. extract the `e_1`-coefficient of `(p−N)²=|J|²(p−N)` ⟹ **`N(J)=p`**.
Then `J=π` (A4) and the law `(π/π')₃=(π'/π)₃` + the transfer.

## How to verify
`cd lean && lake build E213.Lib.Math.Algebra.CayleyDickson` ; then from repo root
`python3 tools/scan_axioms.py <module>` per module.
