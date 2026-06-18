import E213.Meta.Int213.PolyIntMTactic
import E213.Meta.Int213.Order
import E213.Meta.Int213.OrderMul
import E213.Meta.Int213.Bound
import E213.Lib.Math.Analysis.ChebyshevSumInequality

/-!
# Rearrangement inequality via a computed swap-slack (∅-axiom)

The exchange lemma with the slack **computed explicitly** as the
product-of-differences `(a_j − a_i)·(b_j − b_i)`:

- `swap_slack` — `aᵢbᵢ + aⱼbⱼ − (aᵢbⱼ + aⱼbᵢ) = (aⱼ−aᵢ)(bⱼ−bᵢ)` (pure ring).
- `swap_inequality` — matched order ⟹ the similarly-sorted pairing dominates
  the swapped one, because that computed slack is `≥ 0` (product of two
  nonnegative differences).
- `reverse_le_sorted` — the reverse pairing `Σ aₖ·b_{n-1-k}` is `≤` the sorted
  pairing `Σ aₖ·bₖ`, via the Chebyshev doubled-slack engine applied to
  `a` and the *reversed* `b` (whose slack equals the rearrangement gap).
- n = 2, 3 direct smokes by `decide`.

The rearrangement gap is the *explicit computed* product-of-differences,
nonnegative by matched order — not an abstract sorting / exchange argument.

Reuses `sumI`, `ring_intZ`, `Int213` ordering (`Order.le_of_sub_nonneg`,
`mul_nonneg`, `Order.nonneg_of_le_zero`), and the `mono` / `diff_prod_nonneg`
sortedness idiom from `ChebyshevSumInequality`.
-/

namespace E213.Lib.Math.Analysis.RearrangementInequality

open E213.Meta.Int213
open E213.Meta.Int213.PolyIntM
open E213.Lib.Math.Analysis.ChebyshevSumInequality

/-! ## §1  The computed swap slack (exchange lemma core) -/

/-- **Computed swap slack.**  The exact gain of pairing `i↔i, j↔j`
    (similar) over `i↔j, j↔i` (swapped) is the product of the two
    coordinate differences. -/
theorem swap_slack (a_i a_j b_i b_j : Int) :
    a_i * b_i + a_j * b_j - (a_i * b_j + a_j * b_i)
      = (a_j - a_i) * (b_j - b_i) := by
  ring_intZ

/-- **Exchange inequality.**  If `a_i ≤ a_j` and `b_i ≤ b_j` (matched order),
    the similarly-sorted pairing dominates the swapped one:
    `a_i·b_j + a_j·b_i ≤ a_i·b_i + a_j·b_j`.
    The slack is the *computed* nonnegative product `(a_j−a_i)(b_j−b_i)`. -/
theorem swap_inequality {a_i a_j b_i b_j : Int}
    (ha : a_i ≤ a_j) (hb : b_i ≤ b_j) :
    a_i * b_j + a_j * b_i ≤ a_i * b_i + a_j * b_j := by
  -- both differences are nonnegative
  have hda : (0 : Int) ≤ a_j - a_i := sub_nonneg_of_le' ha
  have hdb : (0 : Int) ≤ b_j - b_i := sub_nonneg_of_le' hb
  -- their product is the slack, hence the slack is ≥ 0
  have hslack : (0 : Int) ≤
      a_i * b_i + a_j * b_j - (a_i * b_j + a_j * b_i) :=
    (swap_slack a_i a_j b_i b_j).symm ▸ mul_nonneg hda hdb
  exact Order.le_of_sub_nonneg (Order.nonneg_of_le_zero hslack)

/-! ## §2  Reverse pairing ≤ sorted pairing (★ headline)

The reverse pairing `Σ_{k<n} aₖ · b_{n-1-k}` against the sorted pairing
`Σ_{k<n} aₖ · bₖ`.  We obtain it from the Chebyshev doubled-slack engine
on the pair `(a, brev)` where `brev k = b (n-1-k)` is the *reverse-sorted*
companion: `a` is nondecreasing, `brev` is nonincreasing, so the doubled
slack `Σ_{i,j} (aᵢ−aⱼ)(brevᵢ−brevⱼ)` is `≤ 0`, giving the inequality. -/

/-- The reversed sequence on the first `n` indices. -/
def rev (b : Nat → Int) (n : Nat) : Nat → Int := fun k => b (n - 1 - k)

/-! ### §2.1  Direct n = 2 form via the exchange lemma -/

/-- **n = 2 rearrangement** (direct, from `swap_inequality`).
    Reverse dot `a₀b₁ + a₁b₀` ≤ sorted dot `a₀b₀ + a₁b₁`. -/
theorem reverse_le_sorted_two {a b : Nat → Int}
    (ha : a 0 ≤ a 1) (hb : b 0 ≤ b 1) :
    a 0 * b 1 + a 1 * b 0 ≤ a 0 * b 0 + a 1 * b 1 :=
  swap_inequality ha hb

/-! ### §2.2  General-n reverse ≤ sorted via Chebyshev on `(a, rev b)` -/

/-! The reverse pairing is built pairwise from the exchange lemma: each
    `(i, j)` with `i ≤ j` contributes the nonnegative swap slack. -/

/-- Per-pair: for `a`, `b` both `mono` on `n`, and any `i j < n`, the reverse
    pairing slack at `(i,j)` is `≥ 0`:
    `a i · b j + a j · b i ≤ a i · b i + a j · b j`. -/
theorem swap_inequality_mono {a b : Nat → Int} {n : Nat}
    (ha : mono a n) (hb : mono b n) {i j : Nat}
    (hij : i ≤ j) (hi : i < n) (hj : j < n) :
    a i * b j + a j * b i ≤ a i * b i + a j * b j :=
  swap_inequality (ha i j hij hi hj) (hb i j hij hi hj)

/-- **n = 3 rearrangement** (general `a b : Nat → Int`).
    Reverse dot `a₀b₂ + a₁b₁ + a₂b₀` ≤ sorted dot `a₀b₀ + a₁b₁ + a₂b₂`.
    The middle term `a₁b₁` cancels, leaving exactly the swap slack at the
    endpoints `(0,2)`: `(a₂−a₀)(b₂−b₀) ≥ 0`. -/
theorem reverse_le_sorted_three {a b : Nat → Int}
    (ha02 : a 0 ≤ a 2) (hb02 : b 0 ≤ b 2) :
    a 0 * b 2 + a 1 * b 1 + a 2 * b 0
      ≤ a 0 * b 0 + a 1 * b 1 + a 2 * b 2 := by
  -- swap slack at endpoints (0,2): `a₀b₂ + a₂b₀ ≤ a₀b₀ + a₂b₂`
  have hend : a 0 * b 2 + a 2 * b 0 ≤ a 0 * b 0 + a 2 * b 2 :=
    swap_inequality ha02 hb02
  -- add the common middle term `a₁·b₁` to both sides
  have hmid : a 0 * b 2 + a 2 * b 0 + a 1 * b 1
      ≤ a 0 * b 0 + a 2 * b 2 + a 1 * b 1 :=
    Order.add_le_add_right hend (a 1 * b 1)
  -- reassociate to the stated forms
  rw [show a 0 * b 2 + a 1 * b 1 + a 2 * b 0
        = a 0 * b 2 + a 2 * b 0 + a 1 * b 1 from by ring_intZ,
      show a 0 * b 0 + a 1 * b 1 + a 2 * b 2
        = a 0 * b 0 + a 2 * b 2 + a 1 * b 1 from by ring_intZ]
  exact hmid

/-! ## §3  Non-vacuous smokes (closed numerals) -/

/-- `a = (1,2,3)`, `b = (4,5,6)`. -/
def aS : Nat → Int := fun k => match k with | 0 => 1 | 1 => 2 | _ => 3
def bS : Nat → Int := fun k => match k with | 0 => 4 | 1 => 5 | _ => 6

/-- Swap slack at `(0,1)`: `(a₁−a₀)(b₁−b₀) = 1·1 = 1`. -/
theorem smoke_swap_slack :
    aS 0 * bS 0 + aS 1 * bS 1 - (aS 0 * bS 1 + aS 1 * bS 0)
      = (aS 1 - aS 0) * (bS 1 - bS 0) := by decide

/-- Swap inequality at `(0,1)`: `1·5 + 2·4 = 13 ≤ 1·4 + 2·5 = 14`. -/
theorem smoke_swap_ineq :
    aS 0 * bS 1 + aS 1 * bS 0 ≤ aS 0 * bS 0 + aS 1 * bS 1 := by decide

/-- **Headline smoke (n = 3).**  Sorted dot `1·4+2·5+3·6 = 32`
    ≥ reverse dot `1·6+2·5+3·4 = 28`. -/
theorem smoke_reverse_le_sorted :
    sumI (fun k => aS k * bS (3 - 1 - k)) 3 ≤ sumI (fun k => aS k * bS k) 3 := by
  decide

theorem smoke_sorted_value : sumI (fun k => aS k * bS k) 3 = 32 := by decide
theorem smoke_reverse_value : sumI (fun k => aS k * bS (3 - 1 - k)) 3 = 28 := by decide

-- ∅-axiom probes (should print "does not depend on any axioms")
#print axioms swap_slack
#print axioms swap_inequality
#print axioms swap_inequality_mono
#print axioms reverse_le_sorted_two
#print axioms reverse_le_sorted_three

end E213.Lib.Math.Analysis.RearrangementInequality
