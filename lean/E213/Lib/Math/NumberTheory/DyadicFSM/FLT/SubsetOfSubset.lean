import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Binomial
import E213.Meta.Tactic.NatHelper
import E213.Meta.Nat.NatRing213

/-!
# The subset-of-a-subset / trinomial revision identity (∅-axiom)

`C(n,k)·C(k,j) = C(n,j)·C(n−j,k−j)` for `j ≤ k ≤ n` (`choose_mul_choose`) — choosing
a `k`-subset then a `j`-subset of it equals choosing the `j`-subset first then the
remaining `k−j` from the other `n−j` elements.  Both sides equal the trinomial
coefficient `n!/(j!(k−j)!(n−k)!)`.

Genuinely deep with the corpus's *recursive* (Pascal) `choose`: the factorial proof
is unavailable, so the proof goes by the **absorption chain**.  In subtraction-free
additive variables `a=j, b=k−j, c=n−k`,
`add_form : C(a+b+c,a+b)·C(a+b,a) = C(a+b+c,a)·C(b+c,b)` is proved by induction on `a`,
each step multiplying by `(a+1)` and applying the absorption identity `choose_succ_mul`
three times, then cancelling `(a+1)`.  The canonical form is a corollary via index
arithmetic.  Genuinely absent.  All ∅-axiom (`Nat.mul_assoc`/`Nat.add_sub_cancel'` leak
propext → `NatRing213.nat_mul_assoc` / `NatHelper.add_sub_of_le`).
-/

namespace E213.Lib.Math.NumberTheory.DyadicFSM.FLT.SubsetOfSubset

open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Binomial
open E213.Tactic.NatHelper (mul_left_cancel_pos add_sub_of_le add_sub_cancel_right)
open E213.Meta.Nat.NatRing213 (nat_mul_assoc)

/-- Base case `a = 0` of the additive form. -/
theorem add_form_base (b c : Nat) :
    choose (0 + b + c) (0 + b) * choose (0 + b) 0
      = choose (0 + b + c) 0 * choose (b + c) b := by
  rw [Nat.zero_add b,
      choose_zero_right b, choose_zero_right (b + c),
      Nat.mul_one, Nat.one_mul]

/-- Index-normalized absorption `(a+1)·C(m+1, a+1) = (m+1)·C(m, a)` (= `choose_succ_mul`). -/
theorem absorb (m a : Nat) :
    (a + 1) * choose (m + 1) (a + 1) = (m + 1) * choose m a :=
  choose_succ_mul m a

/-- LHS absorption reduction (multiply the inductive LHS by `a+1`). -/
theorem lhs_reduce (a b c : Nat) :
    (a + 1) * (choose (a + b + c + 1) (a + b + 1) * choose (a + b + 1) (a + 1))
      = (a + b + c + 1) * (choose (a + b + c) (a + b) * choose (a + b) a) := by
  have ab1 : (a + 1) * choose (a + b + 1) (a + 1) = (a + b + 1) * choose (a + b) a :=
    absorb (a + b) a
  have ab2 : (a + b + 1) * choose (a + b + c + 1) (a + b + 1)
      = (a + b + c + 1) * choose (a + b + c) (a + b) :=
    absorb (a + b + c) (a + b)
  rw [Nat.mul_comm (a + 1) (choose (a + b + c + 1) (a + b + 1) * choose (a + b + 1) (a + 1)),
      nat_mul_assoc (choose (a + b + c + 1) (a + b + 1)) (choose (a + b + 1) (a + 1)) (a + 1),
      Nat.mul_comm (choose (a + b + 1) (a + 1)) (a + 1),
      ab1,
      ← nat_mul_assoc (choose (a + b + c + 1) (a + b + 1)) (a + b + 1) (choose (a + b) a),
      Nat.mul_comm (choose (a + b + c + 1) (a + b + 1)) (a + b + 1),
      ab2,
      nat_mul_assoc (a + b + c + 1) (choose (a + b + c) (a + b)) (choose (a + b) a)]

/-- RHS absorption reduction. -/
theorem rhs_reduce (a b c : Nat) :
    (a + 1) * (choose (a + b + c + 1) (a + 1) * choose (b + c) b)
      = (a + b + c + 1) * (choose (a + b + c) a * choose (b + c) b) := by
  have ab3 : (a + 1) * choose (a + b + c + 1) (a + 1)
      = (a + b + c + 1) * choose (a + b + c) a :=
    absorb (a + b + c) a
  rw [← nat_mul_assoc (a + 1) (choose (a + b + c + 1) (a + 1)) (choose (b + c) b),
      ab3,
      nat_mul_assoc (a + b + c + 1) (choose (a + b + c) a) (choose (b + c) b)]

/-- The additive (subtraction-free) form, by induction on `a`:
    `C(a+b+c, a+b)·C(a+b, a) = C(a+b+c, a)·C(b+c, b)`. -/
theorem add_form : ∀ (a b c : Nat),
    choose (a + b + c) (a + b) * choose (a + b) a
      = choose (a + b + c) a * choose (b + c) b
  | 0,     b, c => add_form_base b c
  | a + 1, b, c => by
    have ih : choose (a + b + c) (a + b) * choose (a + b) a
        = choose (a + b + c) a * choose (b + c) b := add_form a b c
    have e1 : a + 1 + b = a + b + 1 := by ring_nat
    have e2 : a + b + 1 + c = a + b + c + 1 := by ring_nat
    rw [e1, e2]
    apply mul_left_cancel_pos (c := a + 1) (Nat.succ_pos a)
    rw [lhs_reduce a b c, rhs_reduce a b c, ih]

/-- ★ **Subset-of-a-subset / trinomial revision identity**:
    `C(n,k)·C(k,j) = C(n,j)·C(n−j, k−j)` for `j ≤ k ≤ n`. -/
theorem choose_mul_choose (n k j : Nat) (hjk : j ≤ k) (hkn : k ≤ n) :
    choose n k * choose k j = choose n j * choose (n - j) (k - j) := by
  have hk : j + (k - j) = k := add_sub_of_le hjk
  have hn : k + (n - k) = n := add_sub_of_le hkn
  have habc : j + (k - j) + (n - k) = n := by rw [hk, hn]
  have hbc : (k - j) + (n - k) = n - j := by
    have step : ((k - j) + (n - k)) + j = n := by
      rw [Nat.add_comm ((k - j) + (n - k)) j,
          ← Nat.add_assoc j (k - j) (n - k), hk, hn]
    have : ((k - j) + (n - k) + j) - j = (k - j) + (n - k) :=
      add_sub_cancel_right ((k - j) + (n - k)) j
    rw [← this, step]
  have key := add_form j (k - j) (n - k)
  rw [habc, hk] at key
  rw [hbc] at key
  exact key

/-- Smoke: `n=7,k=4,j=2`: `C(7,4)·C(4,2) = C(7,2)·C(5,2)` (`35·6 = 21·10 = 210`). -/
theorem choose_mul_choose_smoke :
    choose 7 4 * choose 4 2 = choose 7 2 * choose (7 - 2) (4 - 2) := by decide

end E213.Lib.Math.NumberTheory.DyadicFSM.FLT.SubsetOfSubset
