import E213.Lib.Math.NumberTheory.SumTwoSquares
import E213.Lib.Math.NumberTheory.TwoSquareTheorem
import E213.Lib.Math.NumberTheory.ModArith.SumOfSquaresObstruction
import E213.Meta.Int213.PolyIntM

/-!
# Sum-of-two-squares characterization, "if" direction (∅-axiom)

Building the easy ("if") direction of the full characterization
"n is a sum of two squares ⟺ every prime ≡ 3 (mod 4) divides n to an even power"
from the multiplicative closure `isSumTwoSq_mul` (Brahmagupta) + the computed
prime witnesses `two_square`.
-/

namespace E213.Lib.Math.NumberTheory.SumTwoSquaresCharacterization

open E213.Lib.Math.NumberTheory.SumTwoSquares
  (isSumTwoSq isSumTwoSq_zero isSumTwoSq_one isSumTwoSq_sq isSumTwoSq_mul smoke_2)
open E213.Lib.Math.NumberTheory.TwoSquareTheorem (two_square_isSumTwoSq natAbs_sq_sum)
open E213.Lib.Math.NumberTheory.ModArith.SumOfSquaresObstruction (not_sum_two_squares_mod4)
open E213.Meta.Int213.PolyIntM (powInt)

/-! ## §1 — base cases -/

/-- `2 = 1² + 1²` is a sum of two squares (re-export of `smoke_2`). -/
theorem two_isSumTwoSq : isSumTwoSq 2 := smoke_2

/-- Any perfect square `k²` is a sum of two squares (`k² + 0²`); re-export. -/
theorem sq_isSumTwoSq (k : Int) : isSumTwoSq (k * k) := isSumTwoSq_sq k

/-! ## §2 — prime ≡ 1 (mod 4) wrapper -/

/-- ★ **Prime `p ≡ 1 (mod 4)` is a sum of two squares** (`isSumTwoSq ↑p`).
    Thin wrapper of `two_square_isSumTwoSq` (the computed Thue/descent witness). -/
theorem prime_one_mod4_isSumTwoSq (p : Nat) (hp : 1 < p)
    (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p) (hmod : p % 4 = 1) :
    isSumTwoSq (p : Int) :=
  two_square_isSumTwoSq p hp hpr hmod

/-! ## §3 — multiply by a square stays a sum of two squares -/

/-- ★ **Square-multiple closure.**  `isSumTwoSq n → isSumTwoSq (k²·n)`.
    Immediate from `isSumTwoSq_mul` + `sq_isSumTwoSq`.  This handles every
    `q ≡ 3 (mod 4)` prime power appearing to an even power: `q^(2f) = (q^f)²`. -/
theorem isSumTwoSq_of_sq_mul (k n : Int) (hn : isSumTwoSq n) :
    isSumTwoSq (k * k * n) :=
  isSumTwoSq_mul (sq_isSumTwoSq k) hn

/-! ## §4 — powers of a sum-of-two-squares (prime-power induction) -/

/-- ★ **Power closure.**  If `m` is a sum of two squares, so is every power
    `powInt m e`.  Induction on `e` via `isSumTwoSq_mul`.  Applied to a prime
    `p ≡ 1 (mod 4)` (or `p = 2`) this gives `isSumTwoSq (p^e)` for all `e`. -/
theorem isSumTwoSq_powInt (m : Int) (hm : isSumTwoSq m) :
    ∀ e : Nat, isSumTwoSq (powInt m e)
  | 0     => isSumTwoSq_one
  | e + 1 => by
      show isSumTwoSq (powInt m e * m)
      exact isSumTwoSq_mul (isSumTwoSq_powInt m hm e) hm

/-- ★ **Prime-power, `p ≡ 1 (mod 4)`.**  `isSumTwoSq (↑p ^ e)` for prime
    `p ≡ 1 (mod 4)`. -/
theorem prime_one_mod4_pow_isSumTwoSq (p : Nat) (hp : 1 < p)
    (hpr : ∀ d, d ∣ p → d = 1 ∨ d = p) (hmod : p % 4 = 1) (e : Nat) :
    isSumTwoSq (powInt (p : Int) e) :=
  isSumTwoSq_powInt (p : Int) (prime_one_mod4_isSumTwoSq p hp hpr hmod) e

/-- ★ **`2`-power.**  `isSumTwoSq (2^a)` for all `a`. -/
theorem two_pow_isSumTwoSq (a : Nat) : isSumTwoSq (powInt 2 a) :=
  isSumTwoSq_powInt 2 two_isSumTwoSq a

/-- ★ **Even-power of any prime is a sum of two squares.**  `q^(2f) = (q^f)²`,
    a perfect square, hence a sum of two squares — regardless of `q mod 4`.
    This is the slot that absorbs the `q ≡ 3 (mod 4)` primes in the "if"
    direction. -/
theorem even_pow_isSumTwoSq (q : Int) (f : Nat) :
    isSumTwoSq (powInt q (2 * f)) := by
  -- powInt q (2*f) = powInt q (f + f) = powInt q f * powInt q f
  have h2f : 2 * f = f + f := by rw [Nat.two_mul]
  rw [h2f, E213.Meta.Int213.PolyIntM.powInt_add]
  exact sq_isSumTwoSq (powInt q f)

/-! ## §5 — assembled "if" direction

A product of sum-of-two-squares pieces is a sum of two squares.  Concretely:
`n = 2^a · ∏ p_i^{e_i} · ∏ q_j^{2 f_j}` with `p_i ≡ 1 (mod 4)`, `q_j ≡ 3 (mod 4)`
to even powers — each factor is a sum of two squares (§1–§4), and the product is
closed under `isSumTwoSq_mul`. -/

/-- Product of a list of `Int`s (right fold, empty product `1`).  No Mathlib
    `List.prod` (no Mathlib import allowed). -/
def prodInt : List Int → Int
  | []      => 1
  | x :: xs => x * prodInt xs

/-- ★★ **List-fold assembly.**  If every entry of a list of `Int`s is a sum of
    two squares, so is their product.  This is the structural backbone of the
    "if" direction: feed in `[2^a, p_1^{e_1}, …, q_1^{2f_1}, …]`. -/
theorem isSumTwoSq_prodInt :
    ∀ (l : List Int), (∀ x ∈ l, isSumTwoSq x) → isSumTwoSq (prodInt l)
  | [],      _ => by
      show isSumTwoSq 1
      exact isSumTwoSq_one
  | x :: xs, h => by
      show isSumTwoSq (x * prodInt xs)
      have hx : isSumTwoSq x := h x (List.mem_cons_self x xs)
      have hxs : isSumTwoSq (prodInt xs) :=
        isSumTwoSq_prodInt xs (fun y hy => h y (List.mem_cons_of_mem x hy))
      exact isSumTwoSq_mul hx hxs

/-! ## §6 — the elementary "only if" obstruction (mod 4)

The full "only if" direction (every prime `q ≡ 3 (mod 4)` divides `n` to an even
power) rides on the inert-prime fact `q ∣ a²+b² ⟹ q ∣ a ∧ q ∣ b`, which needs the
Euler-criterion non-residue direction (`−1` is a non-residue mod `q ≡ 3 (mod 4)`)
— not cleanly available here.  The *elementary* slice IS available and closes
∅-axiom: a sum of two squares is never `≡ 3 (mod 4)`.  This already rules out the
simplest `q ≡ 3 (mod 4)` obstructions (`3`, `7`, `11`, …) as non-representable. -/

/-- ★★ **"Only if" fragment (mod 4).**  If `isSumTwoSq n`, then `n.natAbs % 4 ≠ 3`.
    The `Int`-level lift of `not_sum_two_squares_mod4`, via `natAbs_sq_sum`. -/
theorem isSumTwoSq_natAbs_mod4_ne_three {n : Int} (hn : isSumTwoSq n) :
    n.natAbs % 4 ≠ 3 := by
  obtain ⟨a, b, hab⟩ := hn
  rw [hab, natAbs_sq_sum]
  exact not_sum_two_squares_mod4 a.natAbs b.natAbs

/-- ★ **`3` is not a sum of two squares** (`3 ≡ 3 mod 4`). -/
theorem not_isSumTwoSq_three : ¬ isSumTwoSq 3 := by
  intro h
  exact isSumTwoSq_natAbs_mod4_ne_three h (by decide)

/-- ★ **`7` is not a sum of two squares** (`7 ≡ 3 mod 4`). -/
theorem not_isSumTwoSq_seven : ¬ isSumTwoSq 7 := by
  intro h
  exact isSumTwoSq_natAbs_mod4_ne_three h (by decide)

/-! ## §7 — numeric smokes (closed numerals) -/

/-- `25 = 5² + 0²` (perfect square). -/
theorem smoke_25 : isSumTwoSq 25 := ⟨5, 0, by decide⟩
/-- `25 = 4² + 3²` (the genuine two-square rep of `5²`). -/
theorem smoke_25' : isSumTwoSq 25 := ⟨4, 3, by decide⟩
/-- `45 = 6² + 3² = 36 + 9` (`= 9·5 = 3²·5`). -/
theorem smoke_45 : isSumTwoSq 45 := ⟨6, 3, by decide⟩
/-- `50 = 7² + 1² = 49 + 1` (`= 2·25`). -/
theorem smoke_50 : isSumTwoSq 50 := ⟨7, 1, by decide⟩

/-- `45 = 3²·5` obtained by closure: `5` is a sum of two squares, multiplied by `3²`. -/
theorem smoke_45_via_closure : isSumTwoSq 45 := by
  have h5 : isSumTwoSq 5 := ⟨2, 1, by decide⟩
  have : isSumTwoSq ((3 : Int) * 3 * 5) := isSumTwoSq_of_sq_mul 3 5 h5
  show isSumTwoSq 45
  have he : (3 : Int) * 3 * 5 = 45 := by decide
  rw [he] at this; exact this

/-- `50 = 2·25` obtained by closure: `2` and `25` are each a sum of two squares. -/
theorem smoke_50_via_closure : isSumTwoSq 50 := by
  have : isSumTwoSq ((2 : Int) * 25) := isSumTwoSq_mul two_isSumTwoSq smoke_25
  show isSumTwoSq 50
  have he : (2 : Int) * 25 = 50 := by decide
  rw [he] at this; exact this

end E213.Lib.Math.NumberTheory.SumTwoSquaresCharacterization
