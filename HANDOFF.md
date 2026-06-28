# Session Handoff — 2026-06-26 (continuation)

## Branch
`claude/handoff-continuation-dqjw6i` — ahead of origin (push at session end).
Full `lake build E213.Lib.Math.Algebra.CayleyDickson` clean.  ∅-axiom standard: every theorem this
session is **PURE** (`#print axioms` → "does not depend on any axioms").  Purity-check: 0 sorry / 0
external axiom / 0 native_decide / 0 Classical / 0 Mathlib / **0 propext**.

## Headline — the cubic reciprocity law is assembled (PURE)

`EisensteinCubicReciprocity.cubic_reciprocity_law` (capstone): for a primary Jacobi prime `J = π`
(norm `p`) and a second rational prime `q ≡ 2 (mod 3)` (inert), the **cubic residue symbol**
`(π/q)₃` — the `μ₃` value of `J^{(q²−1)/3} mod q` — is **well defined** and **equals** the cubic
character `χ(q) = (q/π)₃`.  Bundles three facts:
1. `χ(q) ∈ {1, ω, ω²}`  (`chiOmega_unit_value`);
2. `J^{(q²−1)/3} ≡ χ(q) (mod q)`  (`cubic_reciprocity_power_congr`, the Gauss-sum Frobenius collapse);
3. **well-definedness**: any `μ₃` value `V ≡ J^{(q²−1)/3} (mod q)` equals `χ(q)` (`mu3_eq_of_modEq`).

`residue_symbol_exists`: `J^{(q²−1)/3}` lands in `μ₃` mod `q` (its cube is `J^{q²−1} ≡ χ(q)³ = 1`,
the congruence cubed → `inert_cube_one_value`).  With (3) the value is pinned to `χ(q)`.

`(π/q)₃ = χ(q) = (q/π)₃` is the cubic reciprocity relation.  The full chain — Jacobi core →
Gauss-sum Frobenius → exponent collapse → **inert prime in ℤ[ω]** → **cube-splitting** → **μ₃ lift**
— is ∅-axiom (PURE).

## What was done this session (5 new PURE bricks)

The prior handoff had the exponent collapse `J^{(q²−1)/3} ≡ χ(q)` done but flagged the finish as
blocked on a "PURE Int↔Nat divisibility wall" + the residue-symbol layer.  **The wall was illusory**
(`PolyRoot.IntEuclid.int_dvd_to_nat` is already PURE, via the PURE `natAbs_mul`).  With that, the whole
residue-symbol layer fell:

1. **`EisensteinMu3Lift.mu3_eq_of_modEq`** — a `mod q` congruence between cube roots of unity is an
   equality (`X ≡ Y (mod q), X,Y ∈ μ₃, q > 1 ⟹ X = Y`).  Each distinct pair leaves a `±1` coordinate
   in `X−Y`; `q ∣ (±1)` reflected to ℕ (`int_dvd_to_nat`) is absurd for `q > 1`.

2. **`EisensteinInertForm.normSq_ne_of_mod3_two`** — the inert obstruction over ℤ: `‖d‖² ≠ q` for
   `q ≡ 2 (mod 3)`.  `‖d‖² = (a+b)² − 3ab ≡ (a+b)² (mod 3)`, a square, never `≡ 2`.  Bricks:
   `int_sq_mod3` (`3 ∣ s² ∨ 3 ∣ (s²−1)`), `mod3_sq_ne_two`.  propext-free `¬(3∣1)`/`¬(3∣2)` via
   `Pow213.le_of_dvd_pos` (Nat `∣` `decide` leaks propext — avoided; Nat `≤`/`<`/`=` `decide` is PURE).

3. **`EisensteinInertPrime`** — a rational prime `q ≡ 2 (mod 3)` is **prime in ℤ[ω]**, so
   `ℤ[ω]/(q) ≅ 𝔽_{q²}` is a field.  `inert_norm_prime_euclid` (`q ∣ αβ ⟹ q∣α ∨ q∣β`): same
   Euclidean-gcd dichotomy as the split `norm_prime_euclid`, but `‖d‖² ∈ {1,q,q²}` (`dvd_prime_sq`)
   with the middle norm-`q` branch killed by the inert obstruction.  `inert_residue_no_zero_divisors`.
   (Uses PURE `NatHelper.mul_assoc`; `Nat.mul_assoc` leaks propext.)

4. **`EisensteinInertCube.inert_cube_one_value`** — cube roots of unity in `𝔽_{q²}` are `1, ω, ω²`
   (`y³ ≡ 1 (mod q) ⟹ y ∈ {1,ω,ω²} mod q`).  Inert mirror of `cube_one_value`: `cubic_factor` +
   `inert_residue_no_zero_divisors` (twice).

5. **`EisensteinCubicReciprocity`** — the capstone above.

## Also done — primary normalisation purified + symbol packaged as `∃!`

- **`jacobi_primary` / `exists_unique_primary` are now PURE** (were propext-dirty).  The leak was the
  Lean-core `Int`-`∣` `decide`; replaced with a ℕ-side `beq` reflection toolkit in `EisensteinPrimary`
  (`dvd3_true`/`dvd3_false`/`isPrimary_of`/`not_isPrimary_{re,im}`, all PURE).  Also fixed an
  `Int.mul_sub` (propext) → `ring_intZ` calc in `jacobi_primary`.  **The transfer's first blocker is
  cleared.**
- **`cubic_residue_symbol_well_defined`**: the residue symbol is the *unique* μ₃ value `≡ J^{(q²−1)/3}`,
  namely `χ(q)` (explicit `∃`-unique form; `∃!` notation is Mathlib-only, unavailable here).

## Split-prime arc (Phase B2f) — the second-prime-split Frobenius is built (PURE)

Toward `(π/π')₃ = (π'/π)₃` (both primes Eisenstein), the second prime `π'` is *split*
(`pr = ‖π'‖² ≡ 1 mod 3`), so the analysis is **modulo `π'`** (`ℤ[ω]/(π') ≅ 𝔽_{p'}`, `p'`-power
Frobenius) — the parallel of the inert B2e arc.  Done this session, all PURE:
- **`EisensteinSplitFermat.split_fermat`**: `z^{pr} ≡ z (mod π')` — Fermat in `𝔽_{p'}` (the split
  analog of `frob_sq_modEq`).  Helper `modEq_descend` (ModEq descends to divisors of the modulus).
- **`EisensteinCubicCharPow.chiOmega_pow_p`**: `χ(t)^{pr} = χ(t)` for `pr ≡ 1 mod 3` (identity, vs the
  inert conjugate).
- **`EisensteinConvGaussFrobenius.gauss_pow_modEq_char`**: `g(χ)^{⋆pr}(k) ≡ Σ_t χ(t)·e_{(t·pr)%p}(k)
  (mod ofInt pr)` (split first half).
- **`EisensteinConvGaussReindex`** (4 thms): `gauss_char_reindex_collapse`,
  `gauss_pow_modEq_char_reindexed`, `char_reindex_split`, **`gauss_pow_modEq_char_factored`** —
  **`g(χ)^{⋆pr}(k) ≡ χ̄(pr)·χ(k) (mod ofInt pr)`**, the split factored Frobenius (mirror of
  `gauss_pow_modEq_factored`; note the `χ ↔ χ̄` swap).

## Split reciprocity congruence — DONE (PURE), the split "engine"

The split-prime cube-side chain is complete (`pr = 3(s+1)+1 ≡ 1 mod 3`, the second prime split):
- **`EisensteinCharSumRange.chiOmega_sumRange_zero`**: `Σ_{t<p} χ_ω(t) = 0` (`sumRange` form, the
  scaling argument via `rangeList_mul_lperm`).
- **`EisensteinYfunGauss.Yfun_conv_gauss`**: `Yfun ⋆ g = p·g` (`Yfun = −1 + p·δ₀`; the `−1` part is
  `Σχ = 0` after the reflection reindex `rangeList_refl_lperm`; the `p·δ₀` part is the single `p·g(k)`).
- **`EisensteinSplitCube.gauss_convPow_split`**: `g(χ)^{⋆(3(s+1)+1)} = J^{s+1}·p^{s+1}·g` (cube side;
  the extra `⋆g` turns the trailing `Yfun` into `Yfun⋆g = p·g`).
- **`EisensteinSplitReciprocity.split_reciprocity_congr`**: **`J^{s+1}·p^{s+1} ≡ χ̄(pr) (mod ofInt pr)`**
  — the split analog of `cubic_reciprocity_congr` (cube side `=` Frobenius side at `k=1`; `g(1)=χ(1)=1`
  is the unit cancellation; character conjugated `χ̄(pr)` vs inert `χ(q)`).

## Done (PURE): the all-Eisenstein form + descent to `𝔽_{p'}`

- **`split_reciprocity_congr_eisenstein`**: `J^{2(s+1)}·J̄^{s+1} ≡ χ̄(pr) (mod ofInt pr)` (eliminate
  `p = J·J̄`; split analog of `cubic_reciprocity_congr_eisenstein`).
- **`split_reciprocity_congr_pi`**: descends it to `mod π'` for an Eisenstein prime `π'` of norm `pr`
  (`π' ∣ ofInt pr` via `mul_conj_self` + `modEq_descend`).  The congruence now lives in
  `𝔽_{p'} = ℤ[ω]/(π')`.

## Also done (PURE): residue symbol μ₃-valued + the conjugate-symbol relation

The `J̄`-elimination — which seemed blocked (no inert-style Frobenius for split `π'`) — is **done
correctly**, in `EisensteinSplitResidueSymbol`:
- **`split_residue_cube_one`**: `J^{3(s+1)} ≡ 1 (mod π')` — so `(π/π')₃ := J^{s+1} mod π'` is μ₃-valued.
  Via `split_fermat` (`J^{pr} ≡ J`) + right-cancel `J` (a unit mod `π'`: `jacobi_ne_zero_mod_pi`,
  `π' ∤ J` else `pr ∣ p`).  Helpers `modEq_cancel_right` (cancellation in the domain `ℤ[ω]/(π')`).
- **`split_conj_residue_relation`**: **`J̄^{s+1} ≡ χ̄(pr)·J^{s+1} (mod π')`** — multiply the all-Eisenstein
  congruence by `J^{s+1}` and collapse `J^{3(s+1)} ≡ 1`.  Symbol form `(π̄/π')₃ = χ̄(pr)·(π/π')₃`.  No
  inert-Frobenius guess — the cube-root collapse does the `J̄`-elimination.

## χ-on-ℤ[ω] infrastructure started (PURE)

The ℤ[ω] cubic character `χ_d(α) = α^m mod d` already exists (`EisensteinCubicChar.char_mul`
multiplicativity, `cubic_char_value` μ₃-valued, `char_cubes_to_one`).  New this round:
- **`EisensteinCharNormSplit.eisChar_norm_split`**: `χ_d(N(π')) ≡ χ_d(π')·χ_d(π̄') (mod d)` — since
  `N(π') = π'·π̄'` as Eisenstein integers (`mul_conj_self`) and `char_mul` is multiplicative.  Relates
  the rational character of the norm to the Eisenstein residue symbols `χ_d(π') = (π'/π)₃`, `χ_d(π̄')`.

## BOTH HALVES of cubic reciprocity are built (PURE)

Two clean congruences, **in the two prime moduli**, are now in hand — decomposed into verifiable pieces:
- **mod `π'`** (`split_conj_residue_relation`): `J̄^{s+1} ≡ χ̄(pr)·J^{s+1}`, i.e. `(π̄/π')₃ = χ̄(pr)·(π/π')₃`.
- **mod `d` (`= π`)** (`chiOmega_norm_eq_symbol_product`): `χ_ω(N(π')) ≡ χ_d(π')·χ_d(π̄')`, i.e. the
  rational character of the norm = the product of the Eisenstein residue symbols `(π'/π)₃·(π̄'/π)₃`.
  Built from `chiOmega_eq_eisChar` (`𝔽_p` char = ℤ[ω] char of the embedded integer) + `eisChar_norm_split`.

## ★★★★★ CUBIC RECIPROCITY — the split case is COMPLETE and PURE (Phase B2h–B2q, this session)

**`EisensteinCubicReciprocitySplit.split_cubic_reciprocity`** — for two distinct primary Eisenstein
primes `J = jacobiSum p m x` (norm `p`) and `J₂ = jacobiSum pr m₂ x₂` (norm `pr`), both `≡ 1 (mod 3)`,
the cubic residue symbols are **equal**:  `(J/J₂)₃ = (J₂/J)₃`, i.e. `A = S` for `J^{m₂} ≡ A (mod d₂)`,
`J₂^{m} ≡ S (mod d)`.  `#print axioms → "does not depend on any axioms"` (strict ∅-axiom).

**No proof-assistant formalization of cubic reciprocity exists anywhere** (Mathlib has only Jacobi/Gauss
infrastructure + quadratic reciprocity) — this is **novel**.  Together with the inert
`cubic_reciprocity_law` (`(π/q)₃ = χ(q)` for `q ≡ 2 mod 3`), both cases of the cubic reciprocity law are
now formalized ∅-axiom.

**The assembled derivation** (all μ₃ literals; `C = χ_{d₂}(p)`, `E = χ_d(pr)` rational characters):
- equation (I) `C = conj E·A²` : relation A (`split_conj_residue_relation`, mod d₂) + norm-mult
  (`char_norm_mult`, mod d₂), combined by `combine_relation`.
- equation (II) `E = conj C·S²` : the swapped pair (relation B + swapped norm-mult, mod d).
- `mu3_reciprocity_algebra` (finite μ₃ group step) closes `A = S`.

The source REU note's literal equations were OCR-garbled (its "conjugate law" `χ_π(ᾱ)=conj χ_π(α)` is
false); the honest derivation — corrected & verified — is in
`research-notes/frontiers/cubic_reciprocity_synthesis_from_IR.md`.

### The 9 PURE bricks built this session (all ∅-axiom)
1. **B2h** relaxation `pr < p → pr ≠ p / ¬ p ∣ q` across the split arc (`chiOmega_*_gen`,
   `char_reindex_split`, `gauss_pow_modEq_char_factored`, `split_reciprocity_congr{,_eisenstein,_pi}`,
   `jacobi_ne_zero_mod_pi`, `split_residue_cube_one`, `split_conj_residue_relation`).
2. **B2i** `split_conj_residue_relation_B` — relation B (swapped instantiation, mod d).
3. **B2j/B2k** `split_residue_symbol_exists{,_B}` — both symbols μ₃-valued.
4. **B2l** `mu3_eq_of_modEq_pi` — Eisenstein-modulus μ₃ lift (norm-3 difference).
5. **B2m** `conj_modEq` (`EisensteinConjModEq`) — the honest conjugate law `A≡B mod d ⟹ conj A≡conj B mod conj d`.
6. **B2n** `mu3_reciprocity_algebra` — the finite-group closer `C=conj E·A² ∧ E=conj C·S² ⟹ A=S`.
7. **B2o** `chiOmega_eq_eisChar_gen` — relax `χ_ω = χ_d` to any unit `¬ p ∣ t`.
8. **B2p** `char_norm_mult` — `χ_{d₂}(p) ≡ J^{m₂}·(conj J)^{m₂} (mod d₂)`.
9. **B2q** `split_cubic_reciprocity` — the capstone (+ `chiOmega_unit_value_gen`, `combine_relation`,
   `mu3_conj`, `mu3_mul`).

### Promoted to `theory/` (DONE)
The cubic-reciprocity arc is **promoted**: `theory/math/numbertheory/cubic_reciprocity.md` (new chapter,
both cases, ∅-axiom, full synthesis narrative + key-results table).  `cubic_residue_and_jacobi_sum.md`
(foundations) status + open-frontier updated to point at the closed law; frontier notes
`cubic_reciprocity_law.md` / `cubic_reciprocity_synthesis_from_IR.md` marked CLOSED; `theory/math/INDEX.md`
numbertheory listing updated.  `split_cubic_reciprocity_symbol` (self-contained "single common μ₃ value"
form) added (B2r).  Remaining tidy (optional, next session): the formal `process`-skill archive of the
closed frontier notes to `research-notes/archive/`; STRICT_ZERO_AXIOM.md does not currently catalog the
Eisenstein cluster (pre-existing — neither did the foundations chapter).

### (historical) the path, now closed
**The combination closes — proven by Lean.**  The full derivation was worked out and the closing
finite-group step is built and PURE (`mu3_reciprocity_algebra`).

**The closing derivation (all μ₃ literals; `J = π = jacobiSum p m x`, `J₂ = π' = jacobiSum pr m₂ x₂`):**
- `A := (π/π')₃ = J^{m₂} mod π'`,  `B := (π̄/π')₃ = (conj J)^{m₂} mod π'`  (`m₂ = (pr−1)/3`)
- `S := (π'/π)₃ = J₂^{m} mod π`,  `T := (π̄'/π)₃ = (conj J₂)^{m} mod π`  (`m = (p−1)/3`)
- `E := χ_π(pr) = chiOmega p m x pr`,  `C := χ_{π'}(p) = chiOmega pr m₂ x₂ p`  (rational chars, μ₃ literals)
- relation A: `B = conj(E)·A` (mod π');  relation B: `T = conj(C)·S` (mod π)
- norm-mult: `C = A·B` (mod π');  `E = S·T` (mod π)   [`χ_{π'}(N(π)) = χ_{π'}(π)·χ_{π'}(π̄)`]
- substitute: `C = conj(E)·A²`,  `E = conj(C)·S²`  ⟹  **`A = S`** (`mu3_reciprocity_algebra`). ∎

**DONE this session (8 PURE bricks):**
1. **Relaxation `pr < p` → `pr ≠ p` / `¬ p ∣ q`** across the split arc (B2h) — `chiOmega_*_gen`,
   `char_reindex_split`, `gauss_pow_modEq_char_factored`, `split_reciprocity_congr{,_eisenstein,_pi}`,
   `jacobi_ne_zero_mod_pi`, `split_residue_cube_one`, `split_conj_residue_relation`.  Lets relations A & B
   coexist (A uses the first prime as unit arg, B the second).
2. **Relation B** `split_conj_residue_relation_B` (B2i) — swapped instantiation, mod π.
3. **Both symbols μ₃-valued** `split_residue_symbol_exists{,_B}` (B2j, B2k) — `(π/π')₃, (π'/π)₃ ∈ {1,ω,ω²}`.
4. **Eisenstein μ₃-lift** `mu3_eq_of_modEq_pi` (B2l) — μ₃ congruence mod π' is equality (norm-3 difference).
5. **Conjugate-modulus bridge** `conj_modEq` (B2m) — `A≡B mod d ⟹ conj A≡conj B mod conj d` (honest
   "conjugate law"; `EisensteinConjModEq`).
6. **μ₃ reciprocity algebra** `mu3_reciprocity_algebra` (B2n) — `C=conj E·A² ∧ E=conj C·S² ⟹ A=S`.

**Bricks 7–9 (assembly) — DONE this session** (B2o `chiOmega_eq_eisChar_gen`, B2p `char_norm_mult`,
B2q `split_cubic_reciprocity`).  The law is complete and PURE.

## Three-tier state (per `CLAUDE.md` "Three-tier discipline")
- **Promotions this session**: none yet — Phase B's promotable unit is the *law*, now assembled; the
  arc (`Eisenstein{Mu3Lift,InertForm,InertPrime,InertCube,CubicReciprocity}` + the prior Gauss-sum
  Frobenius files) is a **promotion candidate** to `theory/` once the `π↔π'` transfer closes the
  frontier (`theory/PROMOTION_CRITERIA.md` H1–H4 + S1–S3).
- **Active scratchpad**: `research-notes/frontiers/cubic_reciprocity_law.md` (updated with B2e finish).

## File Map (this session)
```
NEW (Lean, all PURE):
  lean/.../CayleyDickson/Integer/EisensteinMu3Lift.lean          ← μ₃ lift (X≡Y mod q ⟹ X=Y)
  lean/.../CayleyDickson/Integer/EisensteinInertForm.lean        ← inert obstruction ‖d‖² ≠ q
  lean/.../CayleyDickson/Integer/EisensteinInertPrime.lean       ← q prime in ℤ[ω] (𝔽_{q²} field)
  lean/.../CayleyDickson/Integer/EisensteinInertCube.lean        ← cube roots of unity = {1,ω,ω²}
  lean/.../CayleyDickson/Integer/EisensteinCubicReciprocity.lean ← capstone: (π/q)₃ = χ(q)
MODIFIED:
  lean/E213/Lib/Math/Algebra/CayleyDickson.lean                 ← aggregator imports (5 new)
  research-notes/frontiers/cubic_reciprocity_law.md             ← B2e finish + transfer scope
```

## Operating reminders (carried)
- **PURE is mandatory** — `#print axioms → "does not depend on any axioms"`.  `propext` is **not**
  allowed (its "always allowed" clause is only Lean-core wf-recursion, not avoidable leaks).  Recurring
  propext sources to avoid: `Nat.mul_assoc`, `Int.{mul_comm,zero_add,add_comm,add_assoc,mul_one,
  sub_zero,zero_sub}`, `Nat`-`∣` `decide`, `Int.{ofNat_dvd,natAbs_mul,natAbs_dvd_natAbs}`,
  `Nat.dvd_one`.  PURE substitutes: `NatHelper.mul_assoc`, `Int213.*`, `IntEuclid.{natAbs_mul,
  int_dvd_to_nat,nat_dvd_to_int}`, `Pow213.le_of_dvd_pos`, `CoprimeMultiplicative.eq_one_of_dvd_one`.
- `ring_intZ` is PURE but **cannot fold constant-zero products** (`z*0`, `0*0`, `x-0`) — use explicit
  `Int.mul_zero` / `Int213.zero_mul` / `Int.{sub_eq_add_neg,neg_zero,add_zero}` per component.
- `set` is a **Mathlib** tactic — unavailable; use helper lemmas or write expressions out.
- Never amend commits; never push to `main`; English-only repo artifacts.
