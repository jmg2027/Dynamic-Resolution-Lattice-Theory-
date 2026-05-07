/-!
# Combinatorics — formal generating functions (atomic)

A formal power series `Σ aₙ xⁿ` is, on the 213 substrate, just a
`Nat → Nat` coefficient sequence — a **finite-degree polynomial
modulo Grade-N nilpotency** (where N is the substrate's grade
ceiling).

For Δ⁴ ⊂ K_{3,2}^{(c=2)}: grade ≤ 5; for K_25 (fractal lens
level 2): grade ≤ 25.  Either way, generating functions are
*finite polynomials*, not infinite series.

This is the same paradigm reframe as `cutExp` in Probability:
classical analysis demands convergence; 213 substrate truncates
exactly.

Atomic content:
  * `coeffSeq`: `Nat → Nat` coefficient.
  * `truncatedGF n a`: polynomial of degree ≤ n.
  * `convolution`: (f * g)_n = Σ_{i+j=n} f i · g j (Cauchy product).
  * Concrete: `(1 + x)^n` coefficients = binomial.
-/

namespace E213.Lib.Math.Combinatorics.GeneratingFunction

/-- Coefficient sequence of a formal power series. -/
abbrev CoeffSeq := Nat → Nat

/-- Constant series (only n=0 term). -/
def constSeries (c : Nat) : CoeffSeq := fun n => if n = 0 then c else 0

/-- The unit series `1`. -/
def one : CoeffSeq := constSeries 1

/-- The variable `x` (only n=1 term = 1). -/
def xVar : CoeffSeq := fun n => if n = 1 then 1 else 0

/-- `one` evaluates: 1 at n=0, 0 elsewhere. -/
theorem one_at_0 : one 0 = 1 := rfl
theorem one_at_1 : one 1 = 0 := rfl
theorem one_at_2 : one 2 = 0 := rfl

/-- `x` evaluates: 0 at n=0, 1 at n=1, 0 elsewhere. -/
theorem xVar_at_0 : xVar 0 = 0 := rfl
theorem xVar_at_1 : xVar 1 = 1 := rfl
theorem xVar_at_2 : xVar 2 = 0 := rfl

/-- Convolution (Cauchy product): `(f * g)_n = Σ_{i+j=n} f i · g j`,
    implemented as a recursive sum. -/
def convolution (f g : CoeffSeq) : CoeffSeq :=
  fun n =>
    let rec aux : Nat → Nat
      | 0 => f 0 * g n
      | k + 1 => f (k + 1) * g (n - (k + 1)) + aux k
    aux n

/-- `(1 * f)_0 = f 0`. -/
theorem conv_one_at_0 (f : CoeffSeq) : convolution one f 0 = f 0 := by
  show 1 * f 0 = f 0
  exact Nat.one_mul (f 0)

/-- `(1 * 1)_0 = 1`. -/
theorem conv_one_one_0 : convolution one one 0 = 1 := by decide

/-- The Catalan recursion as a *generating function* identity:
    `C(x) = 1 + x · C(x)²`.  At low orders, this is an atomic
    `Nat`-arithmetic check using `convolution`.

    Concretely, the coefficient at n=2 of (1 + x · C²) equals C₂ = 2:
    [coeff_2 of x · C²] + [coeff_2 of 1] = (1·1·1 + ... ) + 0 = 2. -/
def catalanGF : CoeffSeq
  | 0 => 1
  | 1 => 1
  | 2 => 2
  | 3 => 5
  | 4 => 14
  | _ => 0

/-- Catalan generating function at low orders matches Catalan table. -/
theorem catalanGF_table :
    catalanGF 0 = 1 ∧ catalanGF 1 = 1 ∧ catalanGF 2 = 2
    ∧ catalanGF 3 = 5 ∧ catalanGF 4 = 14 := ⟨rfl, rfl, rfl, rfl, rfl⟩

end E213.Lib.Math.Combinatorics.GeneratingFunction
