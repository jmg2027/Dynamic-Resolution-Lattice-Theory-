# Math Extras — deferral cleanup module index

This sub-cluster closes "honest scope" deferrals from the
2026-05-07 math-track marathon block (PRs #47–#52).  Each item
was originally listed as cosmetic / verbose / funext-blocked;
all are now ∅-axiom term-mode witnesses.

## Modules

| File | Closes deferral from | Status |
|---|---|---|
| `CauchySchwarz.lean` | Measure/INDEX.md, Functional/INDEX.md (Hölder atomic, AM-GM) | ∅-axiom |
| `LpOneCollapse.lean` | Measure/INDEX.md (∀ S form of `‖f‖_1 = ∫ f`) | ∅-axiom |
| `SymFin.lean` | Group/INDEX.md (Sₙ via `Fin n` upgrade of `Nat → Nat`) | ∅-axiom |
| `InnerCauchy.lean` | Functional/INDEX.md (inner-product CS at n=1) | ∅-axiom |
| `Capstone.lean` | 4 cluster witnesses + `total_witness` | ∅-axiom |
| `Extras.lean` | umbrella | — |

## What was closed

### 1. Cauchy-Schwarz (`2·a·b ≤ a² + b²`)

`CauchySchwarz.two_mul_le_sq_add_sq` — proven by case split on
`a ≤ b ∨ b ≤ a`, writing the larger as `smaller + d`, then
applying `cs_expand : a² + (a+d)² = 2·a·(a+d) + d²`.  All
term-mode; `Nat.add_sub_of_le` replaced by
`E213.Tactic.Nat213.add_sub_of_le` to avoid propext leak.

### 2. Lp p=1 ∀-form

`LpOneCollapse.lp_one_eq_lebesgue` — proven by direct *list
induction* on `s : List DyadicBracket`.  No funext, no `congr`,
no `Quot.sound`: the recursion exposes the per-element identity
`f db.midNum ^ 1 = f db.midNum` (= `Nat.pow_one`).

### 3. Sₙ via `Fin n`

`SymFin.swap2`, `swap2_involutive_zero/one` — defined via
`match i.val with | 0 => ... | _ => ...` to avoid `Fin`
decidability machinery (`decide` leaks propext + Quot.sound).
Term-mode `fin2_zero`, `fin2_one` constructed via
`Nat.zero_lt_succ`, `Nat.lt_succ_self`.

### 4. Inner-product Cauchy-Schwarz at n=1

`InnerCauchy.inner_cs_atomic` — `(f₀·g₀)² = f₀²·g₀²` directly
via `E213.Tactic.Nat213.mul_mul_mul_comm_213`.

## Honest residual scope

  * Generic Cauchy-Schwarz `(Σab)² ≤ (Σa²)(Σb²)` for n ≥ 2: the
    sum-side expansion still requires inductive case-on-`Nat.le_total`
    cross terms — manageable but each cross term needs the
    n=1 case applied per pair.  This Capstone covers the
    pointwise base; the Σ-side aggregator is a future pass.
  * Sₙ for n ≥ 3: `swap2`-style witnesses are atomic; full
    `Fin n!`-cardinality work is a separate marathon
    (representation / character theory).
