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

## Remaining work — the `π ↔ π'` transfer (the last frontier)

`cubic_reciprocity_law` gives the **symbol identity** `(π/q)₃ = χ(q)` for `q` a *rational* prime
`≡ 2 (mod 3)`.  The fully symmetric statement `(π/π')₃ = (π'/π)₃` between two *Eisenstein* primes is the
remaining leg:
- **Purify `jacobi_primary`** (`EisensteinPrimary.exists_unique_primary`, the `J = π` normalisation):
  it carries `propext` (buried in a `decide`-heavy case-bash).  Must be PURE before it enters the law.
- **Run the congruence with `π, π'` swapped** and compare the two `μ₃` symbols, using the primary
  normalisation to kill the unit ambiguity, to land `(π/π')₃ = (π'/π)₃`.
- Optional: package `(π/q)₃` as a *defined* symbol `z^{(q²−1)/3} in 𝔽_{q²}` and prove the
  multiplicativity/value laws against it (currently the symbol is "the unique `μ₃` value congruent to
  the power", via `cubic_reciprocity_law` (3)).

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
