import E213.Lib.Math.NumberTheory.PolyRoot.FactorTheorem
import E213.Meta.Int213.Core
import E213.Meta.Int213.Order

/-!
# PolyRoot/CyclotomicPoly — the polynomials `Xᵐ` and `Tᵐ − 1`

The root bound (`RootBound.eval_zero`) is applied to `Tᵐ − 1` to show not every nonzero
residue can be a root (else its constant coefficient `−1` would be `≡ 0 mod p`).

  * `Xp m` / `eval_Xp` / `Xp_length` — `Xᵐ` as a coefficient list, `eval = aᵐ`, length `m+1`.
  * `pmoSucc k` / `eval_pmoSucc` / `pmoSucc_length` — `T^(k+1) − 1`, `eval = a^(k+1) − 1`,
    length `k+2`; constant coefficient `−1`.

All zero-axiom.
-/

namespace E213.Lib.Math.NumberTheory.PolyRoot

/-- `Xᵐ` as a coefficient list (head = constant). -/
def Xp : Nat → List Int
  | 0 => [1]
  | m + 1 => 0 :: Xp m

theorem eval_Xp (a : Int) : ∀ m, eval (Xp m) a = a ^ m := by
  intro m
  induction m with
  | zero =>
    show (1 : Int) + a * eval [] a = a ^ 0
    rw [eval_nil, E213.Meta.Int213.PolyIntM.mul_zeroZ]; rfl
  | succ m ih =>
    show (0 : Int) + a * eval (Xp m) a = a ^ (m + 1)
    rw [ih, E213.Meta.Int213.zero_add, Int.pow_succ, E213.Meta.Int213.mul_comm]

theorem Xp_length : ∀ m, (Xp m).length = m + 1
  | 0 => rfl
  | m + 1 => by show (0 :: Xp m).length = m + 1 + 1; rw [List.length_cons, Xp_length m]

/-- `T^(k+1) − 1` as a coefficient list. -/
def pmoSucc (k : Nat) : List Int := (-1) :: Xp k

theorem eval_pmoSucc (a : Int) (k : Nat) : eval (pmoSucc k) a = a ^ (k + 1) - 1 := by
  show (-1 : Int) + a * eval (Xp k) a = a ^ (k + 1) - 1
  rw [eval_Xp, Int.pow_succ]; ring_intZ

theorem pmoSucc_length (k : Nat) : (pmoSucc k).length = k + 2 := by
  show (Xp k).length + 1 = k + 2
  rw [Xp_length]

/-- The constant coefficient of `T^(k+1) − 1` is `−1`: `eval (pmoSucc k) 0 = −1`. -/
theorem eval_pmoSucc_zero (k : Nat) : eval (pmoSucc k) 0 = -1 := by
  show (-1 : Int) + 0 * eval (Xp k) 0 = -1
  rw [E213.Meta.Int213.zero_mul]; decide


/-- `(1:Int)^k = 1` (pure induction; core `Int.one_pow` is unavailable). -/
theorem one_pow_int : ∀ k : Nat, (1 : Int) ^ k = 1
  | 0 => rfl
  | k + 1 => by rw [Int.pow_succ, one_pow_int k]; decide

/-- ★ **`1` is a root of `Tⁿ − 1`** (`eval (pmoSucc k) 1 = 1^{k+1} − 1 = 0`): every
    `Tⁿ − 1` vanishes at `1`, the trivial `n`-th root of unity. -/
theorem eval_pmoSucc_one (k : Nat) : eval (pmoSucc k) 1 = 0 := by
  rw [eval_pmoSucc, one_pow_int (k + 1)]; decide
end E213.Lib.Math.NumberTheory.PolyRoot
