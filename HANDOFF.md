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
  - `EisensteinCharDiv` (extended): `mul_succ_inv` (`(v+1)·w≡1+w` when `v·w≡1`) and
    **`chiOmega_ratio_term`** (`χ_ω(u)·χ̄_ω((u−1)%p) = χ_ω((1+(u−1)⁻¹)%p)` for `2≤u<p`).
  - **SUM-LEVEL INTEGRATION — in progress (additive-shift route, cleaner than mult-reindex).**
    Off-diagonal `(g⋆ḡ)(k) = ofInt(−1)` for `0<k<p`.  Concrete plan (the wrap `j+k≡0` term vanishes
    since `χ_ω(0)=0`; reindexes are clean unit-permutations):
    - **DONE `Integer/EisensteinGaussShift`** — `add_shift_index` (`((j+k)%p+p−k)%p=j`) +
      **`gauss_offdiag_shift`**: `(g⋆ḡ)(k) = Σ_{j<p} χ_ω((j+k)%p)·χ̄_ω(j)` (reindex `i=(j+k)%p`, the
      one-sided form — NO nasty index helper).
    - **DONE `Integer/EisensteinRangeTotatives`** — `mem_totativeList_prime`,
      `rangeList_perm_cons_totatives`, **`listSum_rangeList_split`** (`Σ_{[0,p)}F = F 0 + Σ_{tot}F`):
      drops the `j=0` term (`χ̄_ω(0)=0`), moving to the units sum the inversion reindex needs.
    - **DONE `Integer/EisensteinShiftTerm`** — **`chiOmega_shift_term`** (the per-term crux, handles the
      wrap): for unit `j`, `χ_ω((j+k)%p)·χ̄_ω(j) = χ_ω((1+(k·j⁻¹))%p)`.  `(j+k)%p≠0`: `chiOmega_div`;
      `(j+k)%p=0`: both sides `χ_ω(0)=0` (same index algebra forces target index `≡0`).
    - **DONE `Integer/EisensteinGaussOffDiagOne`** — `offdiag_const` (`Σ_{z∈tot}χ_ω((1+z)%p)=ofInt(−1)`
      via add-shift perm + split + orthogonality), **`gauss_conj_offdiag`: `(g⋆ḡ)(k)=ofInt(−1)`**
      (`0<k<p`; inversion + mult reindex collapse to `offdiag_const`), and **`gauss_conj_norm`**:
      `(g⋆ḡ)(k) = ofInt(p−1) if k=0 else ofInt(−1)` for `k<p`.  **`g·conj g = p·1 − N` is now PROVEN
      (coefficient form).**

### Phase A3 — REMAINING: `N(J)=p` from `g·ḡ = p·1−N` (TODO 5, the next sub-project)
**Key simplification found:** let `Y := g·conj g` (coeffs `p−1` at `e_0`, `−1` else).  Then
**`Y⋆Y = p·Y`** is *pure convolution combinatorics* (`Y=p·e_0−N`, `N⋆N=p·N`, `e_0` is the conv unit).
And the Gauss–Jacobi relation gives `g²=J·g(χ²)`, `ḡ²=J̄·conj g(χ²)`, with `g(χ²)·conj g(χ²)=Y` (χ² is
also a nontrivial cubic char) ⟹ `Y⋆Y = (g²)⋆(ḡ²) = |J|²·Y`.  Comparing the `e_1`-coefficient
(`Y_1=−1≠0`): `|J|²·(−1) = p·(−1)`, so **`N(J)=|J|²=p`**.  Bricks:
  - **Infra READY:** `conv_add_left`+`conv_add_right` (conv bilinearity), `sum_single` (read off the
    `i₀`-coefficient: `f` vanishes off `i₀<n` ⟹ `Σf = f i₀`), `sum_ones` (`Σ ofInt 1 = ofInt ↑n`),
    `sum_add`/`sum_mul_left`/`sum_congr`, `ofInt_mul`/`ofInt_add`/`ofInt_neg`.
    **⚠ funext-trap recorded:** `Yfun=A+B` as *functions* needs `funext` (Quot-backed, FORBIDDEN); do
    the bilinear expansion *pointwise inside the summand* (`sum_congr`), not via `conv_add_left` on `Yfun`.
    **⚠ ring_intZ-trap:** `ring_intZ` chokes on `(−1)*q` (`(C 1).neg.mul`) — use `neg_mul`+`one_mulZ`.
  - **DONE `Integer/EisensteinNormConv`** — `Yfun`/`Bfun` defs + **`Yfun_conv`: `(Yfun⋆Yfun)(n) =
    ofInt(↑p)·Yfun n`** (= `Y²=p·Y`, pure convolution counting via the pointwise decomposition).  **5a ✓.**
  - **5b ✓ (unit coefficients)** — `Integer/EisensteinGaussJacobiIndex` (`gj_index`, modular negation via
    `neg_mul_mod`), `Integer/EisensteinGaussJacobiTerm` (`gj_term`: `χ(nt)·χ(n(1−t))=χ(n)²·χ(t)·χ(1−t)`,
    `mul_swap_mid`), `Integer/EisensteinGaussJacobi` (`jacobi_eq_listSum`, **`gauss_sq_unit`:
    `(g⋆g)(n)=jacobiSum·χ_ω(n)²` for `0<n<p`**) — i.e. `g(χ)²=J·g(χ²)` at unit coeffs (`g(χ²)(n)=χ_ω(n)²`).
  - **5b-rem** the `n=0` coeff `(g⋆g)(0)=0` (`=J·χ_ω(0)²=0`) — needs `Σ_{i∈tot}χ_ω(i)²=0` (χ²-orthogonality;
    reuse `scale_fixed_eq_zero` with `χ²(a)=χ_ω(a)²∈{ω,ω²}≠1`, `chiOmega_mul` for χ² multiplicativity).
  - **5c** `g(χ²)·conj g(χ²) = Yfun` — reuse `gauss_conj_norm` machinery for the character `χ²=χ̄`.
  - **5d-partial** conv comm **✓** — `Integer/EisensteinConvComm` (`refl_invol`, `rangeList_refl_lperm`,
    **`conv_comm`**: `(f⋆g)(k)=(g⋆f)(k)`, `k<p`).
  - **5d group-ring algebra ✓ COMPLETE** — `Integer/EisensteinConvComm` (`conv_comm`),
    `Integer/EisensteinConvAssocIndex` (`conv_assoc_index`, `neg_add_mod`, `two_sub_mod`, `sub_sub_two`),
    `Integer/EisensteinConvAssoc` (**`conv_assoc`**).  Plus `sum_swap`/`sum_mul_right` in `FiniteSum`.
    **`R[C_p]` convolution is now a verified commutative ring** (bilinear + comm + assoc).
  - **5d group-ring spine ✓ COMPLETE** — `conv_congr` (`EisensteinGroupRing`),
    `conv_four_swap` (`EisensteinConvFourSwap`: `(a⋆b)²=(a⋆a)⋆(b⋆b)`), and **`gg_gbgb_eq`**
    (`EisensteinGaussNormSq`): **`(g⋆g)⋆(ḡ⋆ḡ)(k) = ofInt(↑p)·Yfun p k`** for `k<p` (via reassoc +
    `gauss_conj_eq_Yfun` + `Yfun_conv`).  The structural core of `N(J)=p` is DONE.
  - **5b ✓ FULLY COMPLETE** — `Integer/EisensteinCubicCharSq` (`conj_chiOmega_eq_sq`: `conj χ=χ²`;
    **`chiOmega_sq_orth`**: `Σ_{tot}χ_ω(i)²=0` via conjugation of `χ`-orthogonality),
    `Integer/EisensteinGaussSqZero` (`gauss_sq_zero`: `(g⋆g)(0)=0` via `χ((p−i)%p)=χ(i)` [`p−1` a cube,
    `χ(p−1)=1`] + χ²-orth; **`gauss_sq_full`: `(g⋆g)(n)=jacobiSum·χ_ω(n)²` for ALL `n<p`**).
    **The full Gauss–Jacobi relation `g(χ)²=J·g(χ²)` is DONE.**
  - **5d ✓ COMPLETE — `N(J)=p` PROVEN (∅-axiom).**
    - `Integer/EisensteinConjConv` (`gbgb_eq_conj_gg`: `(ḡ⋆ḡ)(k)=conj((g⋆g)((p−k)%p))`, `conj_sumRange`,
      `conj_conv_index`).
    - `Integer/EisensteinJacobiNormLaw` — `conj_sq_chiOmega` (`conj(χ·χ)=χ`), `chi2_offdiag_one`
      (`Σ conj χ(i)·χ((i+p−1)%p)=−1`, the conj of `(g⋆ḡ)(1)`), **`jacobi_norm`:
      `(jacobiSum p m x).normSq = p`**.  Read the `e_1` coeff of `(g·g)⋆(ḡ·ḡ)` two ways: `gg_gbgb_eq`
      gives `ofInt(↑p)·Yfun 1`; per-term factoring (`gauss_sq_full`+`gbgb_eq_conj_gg`) gives
      `(J·conj J)·ofInt(−1)`; cancel `ofInt(−1)` ⟹ `J·conj J = ofInt(↑p) = ofInt(‖J‖²)` ⟹ **`‖J‖²=p`**.
      `#print axioms jacobi_norm → does not depend on any axioms`.

  **★ The Jacobi-sum norm law `N(J)=p` is DONE.**
  - **A4 (partial) ✓** — `Integer/EisensteinJacobiPrime.jacobi_prime`: **`J` is a prime of `ℤ[ω]`**
    (`J∣α·β ⟹ J∣α ∨ J∣β`, direct from `jacobi_norm` + `norm_prime_euclid`).  So `J=π` up to a unit.
  - **A4-rem** the *primary* normalisation `J ≡ −1 mod 3` (fix the unit ⟹ `J=π` exactly).  Then
    **Phase B** — the cubic reciprocity law `(π/π')₃=(π'/π)₃` + the rational transfer (the deep step;
    classically the congruence `g(χ)^p ≡ …` / the explicit Gauss-sum computation — a fresh large phase).
Then `J=π` (A4) and the law `(π/π')₃=(π'/π)₃` + the transfer.

## How to verify
`cd lean && lake build E213.Lib.Math.Algebra.CayleyDickson` ; then from repo root
`python3 tools/scan_axioms.py <module>` per module.
