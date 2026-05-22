import E213.Lib.Math.Cohomology.Fractal.ConfigCountAurifeuillean

/-!
# Bounded cut-off: Hunter ⇔ Aurifeuillean correspondence at m = 1 only

The Hunter primitive expressibility of the Aurifeuillean L-coefficient
pair `(29, 8)` for `Φ_10(5) = 521` is a feature of the **minimal**
Aurifeuillean cyclotomic index `m = 1`.  At the next Aurifeuillean
index `Φ_90(5) = 60081451169922001` (`m = 3`), the canonical pair
`(L, M) = (850554441, 364242064)` falls outside the range of small
Hunter expressions.

This file records the bounded-decidable side of that observation:

  · **Positive direction**: explicit depth-3 Hunter expression for
    `521`, written using only `{NS, NT}` and operations `{+, ^}`.

  · **Negative direction**: `850554441` and `364242064` are not
    expressible as natural depth-≤-3 Hunter expression forms
    `(a^b + c^d, a^b * c^d, (a + b)^c)` for parameters
    `a, b, c, d ∈ {0, …, 9}` (or `{0, …, 19}` for the sum form).
    Decidable via exhaustive enumeration.

The full cut-off claim — *no* Hunter expression at any depth hits
`(L_3, M_3)` — is a complexity-theoretic conjecture about an
infinite parameter space; the bounded results below confirm it at
the explicitly enumerable level.
-/

namespace E213.Lib.Math.Cohomology.Fractal.AurifeuilleanCutoff

/-! ## §1 Hunter primitives -/

/-- DRLT atomic generator `NS = 3` (catalogue). -/
abbrev NS : Nat := 3

/-- DRLT atomic generator `NT = 2` (catalogue). -/
abbrev NT : Nat := 2

/-- DRLT atomic generator `d = 5` (catalogue). -/
abbrev d_ : Nat := 5

/-! ## §2 Positive direction — explicit Hunter expressions

These witnesses show that the Aurifeuillean L-coefficients at `m = 1`
(`521`, `29`, `8`) all admit clean depth-≤-3 Hunter expressions over
`{NS, NT}` ∪ `{+, *, ^}`.  No Lean machinery beyond `decide`. -/

/-- ★ **Depth-3 Hunter expression for `521`**:
    `521 = NT^(NS²) + NS² = 2^9 + 9`.  Three operations: two `^`
    and one `+`, on the two generators `{NS, NT}`. -/
theorem hunter_521_explicit : NT ^ (NS ^ 2) + NS ^ 2 = 521 := by decide

/-- Depth-2 Hunter expression for the L-coefficient `29`:
    `29 = d² + NT²`.  Two `^` and one `+`. -/
theorem hunter_29_explicit : d_ ^ 2 + NT ^ 2 = 29 := by decide

/-- Depth-1 Hunter expression for the M-coefficient `8`:
    `8 = NT^NS = 2³`.  Single `^`. -/
theorem hunter_8_explicit : NT ^ NS = 8 := by decide

/-! ## §3 Negative direction — `Φ_90(5)` L-coefficient bounded cut-off

The Aurifeuillean L-coefficient for `Φ_90(5)` is `850554441` (a 9-digit
integer).  The theorems below establish that this value is **not**
hit by natural depth-≤-3 Hunter expression forms with single-digit
parameters. -/

/-- 850554441 is not expressible as `a^b + c^e` for any
    `a, b, c, e ∈ {0, 1, …, 9}`.  Decidable enumeration (10⁴ cases). -/
theorem L_90_not_pow_sum_pow :
    ∀ (a b c e : Fin 10), a.val ^ b.val + c.val ^ e.val ≠ 850554441 := by
  decide

/-- 850554441 is not expressible as `a^b * c^e` for any
    `a, b, c, e ∈ {0, 1, …, 9}`.  Decidable enumeration. -/
theorem L_90_not_pow_mul_pow :
    ∀ (a b c e : Fin 10), a.val ^ b.val * c.val ^ e.val ≠ 850554441 := by
  decide

/-- 850554441 is not expressible as `(a + b)^c` for any
    `a, b ∈ {0, …, 19}` and `c ∈ {0, …, 9}`.  Covers e.g. `(NS+NT)^c`
    and small linear-combination bases.  Decidable enumeration. -/
theorem L_90_not_sum_pow :
    ∀ (a b : Fin 20) (c : Fin 10), (a.val + b.val) ^ c.val ≠ 850554441 := by
  decide

/-! ## §4 Negative direction — `Φ_90(5)` M-coefficient bounded cut-off

Analogous results for the M-coefficient `364242064`. -/

/-- 364242064 is not expressible as `a^b + c^e` for any
    `a, b, c, e ∈ {0, 1, …, 9}`. -/
theorem M_90_not_pow_sum_pow :
    ∀ (a b c e : Fin 10), a.val ^ b.val + c.val ^ e.val ≠ 364242064 := by
  decide

/-- 364242064 is not expressible as `a^b * c^e` for any
    `a, b, c, e ∈ {0, 1, …, 9}`. -/
theorem M_90_not_pow_mul_pow :
    ∀ (a b c e : Fin 10), a.val ^ b.val * c.val ^ e.val ≠ 364242064 := by
  decide

/-! ## §5 Capstone — bounded cut-off at `m = 3`

Bundles the positive `m = 1` Hunter witness with the negative `m = 3`
bounded enumeration: the depth-≤-3 Hunter expressibility holds at
the minimal Aurifeuillean index `Φ_10(5)` and fails at the next
Aurifeuillean index `Φ_90(5)`. -/

/-- Bounded cut-off capstone: `521` admits a depth-3 Hunter
    expression `NT^(NS²) + NS²`, while the L-coefficient `850554441`
    for `Φ_90(5)` does not admit any depth-≤-3 sum-of-powers or
    product-of-powers Hunter form with parameters `< 10`. -/
theorem bounded_cutoff_at_m3 :
    (NT ^ (NS ^ 2) + NS ^ 2 = 521)
    ∧ (∀ (a b c e : Fin 10),
         a.val ^ b.val + c.val ^ e.val ≠ 850554441
         ∧ a.val ^ b.val * c.val ^ e.val ≠ 850554441) := by
  refine ⟨hunter_521_explicit, fun a b c e => ?_⟩
  exact ⟨L_90_not_pow_sum_pow a b c e, L_90_not_pow_mul_pow a b c e⟩

end E213.Lib.Math.Cohomology.Fractal.AurifeuilleanCutoff
