import E213.Lib.Math.Analysis.CauchyComplete
import E213.Lib.Math.Analysis.Optimization.CompletenessLoop
import E213.Lib.Math.NumberSystems.Real213.Sum.CutSumTest

/-!
# Full Real213 Cauchy witness for the gradient value sequence (∅-axiom)

`CompletenessLoop` witnessed the asymptotic convergence of the gradient value
`vₖ = F(xₖ) = 1/2ᵏ` at the modulus level (a `Nat`-inequality).  This file gives
the **full Real213 object**: the sequence of *cuts* `vₖ = constCut 1 (2ᵏ) = 1/2ᵏ`
is a genuine `CauchyCutSeq` (`Analysis/CauchyComplete`) — a Cauchy sequence of
Real213 cuts with an **explicit, proven modulus** — i.e. an element of the
Real213 completion.  This is the completeness-LOOP instruction realized as an
actual point of the completed real line.

## The modulus

For the cut test-point `(m,k)` (the rational `m/k`), `vᵢ` evaluates to
`constCut 1 (2ᵢ) m k = decide(1·k ≤ 2ᵢ·m)`.  The modulus is `N m k := k`:
- **interior** `m ≥ 1`: for `i ≥ k`, `1·k = k < 2ᵏ ≤ 2ᵢ ≤ 2ᵢ·m`, so the value is
  `true` and stable (`cs_true`);
- **boundary** `m = 0`: `2ᵢ·0 = 0` so the value is `decide(k ≤ 0)`, already
  constant in `i`.
Hence `cauchy` holds with `N m k = k` (`gradientValueCauchy`).

## The limit, honestly

`cutEq` (`Real213.Core.CutPoset`) is *pointwise* bool equality, and the diagonal
limit differs from the closed zero cut `constCut 0 1` only at the **boundary**
`m = 0` (the standard open/closed Dedekind-cut artifact: the limit is the *open*
`0`).  So a full `cutEq limit (constCut 0 1)` is *not* available — and claiming it
would be false.  What is true and proven: on the **interior** (`m ≥ 1`, the
genuine rational test-points) the limit *is* the zero cut, `= true`
(`gradientValueCauchy_limit_interior`).  Together with the modulus convergence of
`CompletenessLoop` (`value_below`), this pins the limit at the real `0`.

The gradient value of Ricci-type gradient flow thus lands as a bona-fide Cauchy
real, converging to its infimum — the completeness-LOOP, fully in Real213.
-/

namespace E213.Lib.Math.Analysis.Optimization.RealCauchyWitness

open E213.Lib.Math.Analysis.CauchyComplete
open E213.Lib.Math.NumberSystems.Real213.Sum.CutSumTest (constCut)
open E213.Lib.Math.Analysis.Optimization.CompletenessLoop (lt_two_pow_self)

/-- For exponent `e ≥ k` and an interior test-point `m'+1`, the value cut
    `1/2ᵉ` reads `true`: `1·k = k < 2ᵉ ≤ 2ᵉ·(m'+1)`. -/
theorem cs_true (e m' k : Nat) (hke : k ≤ e) :
    constCut 1 (2 ^ e) (m' + 1) k = true := by
  show decide (1 * k ≤ 2 ^ e * (m' + 1)) = true
  rw [Nat.one_mul]
  apply decide_eq_true
  have h1 : k < 2 ^ e := Nat.lt_of_le_of_lt hke (lt_two_pow_self e)
  have h2 : 2 ^ e ≤ 2 ^ e * (m' + 1) := Nat.le_mul_of_pos_right _ (Nat.zero_lt_succ m')
  exact Nat.le_trans (Nat.le_of_lt h1) h2

/-- The value cut `1/2ⁱ` is **stable** past index `k`: for `i ≥ k` it equals the
    value at index `k` (interior: both `true`; boundary `m=0`: both
    `decide(k ≤ 0)`). -/
theorem csConst (m k i : Nat) (hki : k ≤ i) :
    constCut 1 (2 ^ i) m k = constCut 1 (2 ^ k) m k := by
  cases m with
  | zero => rfl
  | succ m' => rw [cs_true i m' k hki, cs_true k m' k (Nat.le_refl k)]

/-- ★★★★★ **The gradient value sequence as a Real213 Cauchy sequence.**
    `vᵢ = constCut 1 (2ⁱ) = 1/2ⁱ`, modulus `N m k = k`; the `cauchy` field is
    discharged by stability past `k` (`csConst`).  A genuine element of the
    Real213 completion — the completeness-LOOP instruction as an actual real. -/
def gradientValueCauchy : CauchyCutSeq where
  cs := fun i => constCut 1 (2 ^ i)
  N := fun _ k => k
  cauchy := by
    intro m k i j hi hj
    show constCut 1 (2 ^ i) m k = constCut 1 (2 ^ j) m k
    rw [csConst m k i hi, csConst m k j hj]

/-- ★★★★★ **The limit is `0` on the interior.**  At every genuine rational
    test-point (`m ≥ 1`) the extracted limit equals the zero cut (`= true`).
    (At the boundary `m = 0` the limit is the *open* `0`, the Dedekind artifact;
    see the module docstring — full pointwise `cutEq` to `constCut 0 1` is not
    available and is not claimed.) -/
theorem gradientValueCauchy_limit_interior (m k : Nat) (hm : 1 ≤ m) :
    gradientValueCauchy.limit m k = true := by
  unfold CauchyCutSeq.limit gradientValueCauchy
  cases m with
  | zero => exact absurd hm (by decide)
  | succ m' => exact cs_true k m' k (Nat.le_refl k)

end E213.Lib.Math.Analysis.Optimization.RealCauchyWitness
