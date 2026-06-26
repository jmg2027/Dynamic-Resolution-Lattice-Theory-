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

## Remaining work — finish the split-split law

`cubic_reciprocity_law` gives `(π/q)₃ = χ(q)` for `q` *rational* inert.  For two Eisenstein primes the
split factored Frobenius (above) is built **up to `gauss_pow_modEq_factored` parity**; what remains
mirrors the inert tail but for the split case (and needs the classical exponent worked out — the inert
`(q²−1)/3` becomes the split `(p'−1)/3`-type residue character):
- the cube/norm assembly (`gauss_pow_succ_*` / `gauss_convPow3` analogs) **mod `ofInt pr`**, then the
  **descent to `mod π'`** (via `split_fermat`'s `π' ∣ ofInt pr`, `modEq_descend`);
- the exponent collapse to the split residue character, the μ₃-lift (`mu3_eq_of_modEq`, reusable), and
- the final `π ↔ π'` comparison using the primary normalisation (`jacobi_primary`, now PURE).

Reference: Ireland–Rosen ch. 9.

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
