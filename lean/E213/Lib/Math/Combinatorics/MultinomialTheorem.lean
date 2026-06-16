import E213.Lib.Math.Combinatorics.BollobasSetPair
import E213.Lib.Math.Combinatorics.Sperner
import E213.Meta.Int213.PolyIntMTactic
import E213.Meta.Nat.PolyNatMTactic

/-!
# Multinomial coefficients (trinomial case) — ∅-axiom

Built on the corpus binomial toolkit:
  * `binom` (Pascal recursion) — `Lib/Physics/Simplex/Counts.lean`
  * `Sperner.binom_mul_fact : binom n k · (k!·(n−k)!) = n!`
  * `BollobasSetPair.binom_ab : binom (a+b) a · (a!·b!) = (a+b)!`
  * `Permutations.fact` — the factorial.

Two genuinely-absent classical facts:
  ★★★ **Product-of-binomials** (structural): `multinom3 a b c = C(a+b+c,a)·C(b+c,b)`,
      proven in the division-free *multiplicative* form
      `multinom3 a b c · (a!·b!·c!) = (a+b+c)!`.
  ★★★ **Trinomial expansion** (n = 2, 3) as `Int` identities via `ring_intZ`.
  ★★  **Row-sum** `Σ_{i+j+k=n} multinom3 i j k = 3^n` for small n (by `decide`).

All ∅-axiom.
-/

namespace E213.Lib.Math.Combinatorics.MultinomialTheorem

open E213.Lib.Physics.Simplex.Counts (binom)
open E213.Lib.Math.Combinatorics.Permutations (fact)
open E213.Lib.Math.Combinatorics.Sperner (binom_mul_fact)
open E213.Lib.Math.Combinatorics.BollobasSetPair (binom_ab)

/-! ## §1 — definition: trinomial coefficient as product of binomials -/

/-- Trinomial coefficient, defined as the recursive product of binomials
    `C(a+b+c, a) · C(b+c, b)` — this is `(a+b+c)! / (a! b! c!)`, built
    division-free.  Choosing the `a`-block out of `a+b+c`, then the `b`-block
    out of the remaining `b+c`. -/
def multinom3 (a b c : Nat) : Nat := binom (a + b + c) a * binom (b + c) b

/-! ## §2 — the multiplicative (division-free) factorial identity -/

/-- ★★★ **Multinomial = product of binomials**, cleared of denominators:

      `multinom3 a b c · (a! · b! · c!) = (a + b + c)!`.

    This is the structural identity `multinom3 a b c = (a+b+c)!/(a!·b!·c!)`
    in subtraction/division-free form.  Two applications of `binom_ab`:
    `C(a+b+c,a)·(a!·(b+c)!) = (a+b+c)!` and `C(b+c,b)·(b!·c!) = (b+c)!`. -/
theorem multinom3_mul_fact (a b c : Nat) :
    multinom3 a b c * (fact a * fact b * fact c) = fact (a + b + c) := by
  -- `binom_ab a (b+c) : binom (a + (b+c)) a · (a! · (b+c)!) = (a+(b+c))!`
  have h1 : binom (a + (b + c)) a * (fact a * fact (b + c)) = fact (a + (b + c)) :=
    binom_ab a (b + c)
  -- `binom_ab b c : binom (b+c) b · (b! · c!) = (b+c)!`
  have h2 : binom (b + c) b * (fact b * fact c) = fact (b + c) := binom_ab b c
  have hassoc : a + b + c = a + (b + c) := by ring_nat
  -- rewrite everything onto `a + (b+c)` and expand `multinom3`
  unfold multinom3
  rw [hassoc]
  -- regroup: (Ca · Cbc) · (a!·b!·c!) = Ca · (a! · (Cbc · (b!·c!)))
  --        = Ca · (a! · (b+c)!) = (a+(b+c))!
  rw [show binom (a + (b + c)) a * binom (b + c) b * (fact a * fact b * fact c)
        = binom (a + (b + c)) a * (fact a * (binom (b + c) b * (fact b * fact c)))
      from by ring_nat,
      h2, h1]

/-- ★★★ **Product-of-binomials identity** (the headline structural form):

      `multinom3 a b c = C(a+b+c, a) · C(b+c, b)`.

    True by definition of `multinom3` — recorded as the named theorem so the
    structural content is explicit.  Together with `multinom3_mul_fact` this
    pins `multinom3` as the unique value with `m·(a!·b!·c!) = (a+b+c)!`. -/
theorem multinom3_eq_binom_prod (a b c : Nat) :
    multinom3 a b c = binom (a + b + c) a * binom (b + c) b := rfl

/-- Symmetric reading: the multiplicative identity is symmetric in `a, b, c`
    even though the *definition* factors asymmetrically.  E.g. choosing the
    `c`-block first gives `C(a+b+c,c)·C(a+b,a)`, with the same product of
    factorials — both equal `(a+b+c)!/(a!b!c!)`.  Witnessed at the
    multiplicative level: both `multinom3 a b c` and `multinom3 c a b` satisfy
    `m·(a!·b!·c!) = (a+b+c)!`. -/
theorem multinom3_sym_mul (a b c : Nat) :
    multinom3 c a b * (fact a * fact b * fact c) = fact (a + b + c) := by
  have h := multinom3_mul_fact c a b
  -- h : multinom3 c a b * (c! * a! * b!) = (c+a+b)!
  have hf : fact c * fact a * fact b = fact a * fact b * fact c := by ring_nat
  have hi : c + a + b = a + b + c := by ring_nat
  rw [hf, hi] at h
  exact h

/-! ## §3 — concrete small-cell tables of the product identity (by `decide`) -/

/-- ★ Concrete trinomial coefficients (the multinomial row for `n = 3`):
    `multinom3` over the cells `i+j+k=3`.  The classic coefficient set
    `{1,1,1,3,3,3,3,3,3,6}`. -/
theorem multinom3_row3 :
    multinom3 3 0 0 = 1 ∧ multinom3 0 3 0 = 1 ∧ multinom3 0 0 3 = 1
    ∧ multinom3 2 1 0 = 3 ∧ multinom3 2 0 1 = 3 ∧ multinom3 0 2 1 = 3
    ∧ multinom3 1 2 0 = 3 ∧ multinom3 1 0 2 = 3 ∧ multinom3 0 1 2 = 3
    ∧ multinom3 1 1 1 = 6 := by decide

/-- ★ Concrete trinomial coefficients for `n = 2`: `{1,1,1,2,2,2}`. -/
theorem multinom3_row2 :
    multinom3 2 0 0 = 1 ∧ multinom3 0 2 0 = 1 ∧ multinom3 0 0 2 = 1
    ∧ multinom3 1 1 0 = 2 ∧ multinom3 1 0 1 = 2 ∧ multinom3 0 1 1 = 2 := by decide

/-- ★ The product-of-binomials identity, concrete table (sanity of the
    factorization at specific cells, `decide`-checked). -/
theorem multinom3_prod_table :
    multinom3 1 1 1 = binom 3 1 * binom 2 1
    ∧ multinom3 2 1 0 = binom 3 2 * binom 1 1
    ∧ multinom3 2 0 1 = binom 3 2 * binom 1 0
    ∧ multinom3 1 2 1 = binom 4 1 * binom 3 2 := by decide

/-! ## §4 — trinomial row-sum  Σ multinom3 = 3^n  (small n, by `decide`) -/

/-- ★★ **Trinomial row-sum** `n = 2`: the six cells `i+j+k=2` sum to `3² = 9`. -/
theorem multinom3_rowsum_2 :
    multinom3 2 0 0 + multinom3 0 2 0 + multinom3 0 0 2
    + multinom3 1 1 0 + multinom3 1 0 1 + multinom3 0 1 1 = 9 := by decide

/-- ★★ **Trinomial row-sum** `n = 3`: the ten cells `i+j+k=3` sum to `3³ = 27`. -/
theorem multinom3_rowsum_3 :
    multinom3 3 0 0 + multinom3 0 3 0 + multinom3 0 0 3
    + multinom3 2 1 0 + multinom3 2 0 1 + multinom3 0 2 1
    + multinom3 1 2 0 + multinom3 1 0 2 + multinom3 0 1 2
    + multinom3 1 1 1 = 27 := by decide

/-! ## §5 — trinomial expansion as `Int` polynomial identities (`ring_intZ`)

Powers written as repeated multiplication (`x*x`), base atoms `x, y, z`.
The multinomial coefficients appear as the literal `Int` numerals matching
`multinom3_row2` / `multinom3_row3`. -/

/-- ★★★ **Trinomial expansion, degree 2**:

      `(x+y+z)² = x² + y² + z² + 2xy + 2yz + 2zx`.

    Coefficients `{1,1,1,2,2,2}` are exactly `multinom3_row2`. -/
theorem trinomial_expand_2 (x y z : Int) :
    (x + y + z) * (x + y + z)
      = x*x + y*y + z*z + 2*(x*y) + 2*(y*z) + 2*(z*x) := by ring_intZ

/-- ★★★ **Trinomial expansion, degree 3** — the full 10-term expansion:

      `(x+y+z)³ = x³+y³+z³ + 3(x²y + x²z + y²x + y²z + z²x + z²y) + 6xyz`.

    Coefficients `{1,1,1, 3,3,3,3,3,3, 6}` are exactly `multinom3_row3`. -/
theorem trinomial_expand_3 (x y z : Int) :
    (x + y + z) * (x + y + z) * (x + y + z)
      = x*x*x + y*y*y + z*z*z
        + 3*(x*x*y) + 3*(x*x*z) + 3*(y*y*x) + 3*(y*y*z) + 3*(z*z*x) + 3*(z*z*y)
        + 6*(x*y*z) := by ring_intZ

end E213.Lib.Math.Combinatorics.MultinomialTheorem
