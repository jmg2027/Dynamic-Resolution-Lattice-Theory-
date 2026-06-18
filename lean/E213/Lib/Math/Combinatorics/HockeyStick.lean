import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Binomial
import E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum

/-!
# The hockey-stick identity `Σ_{i=0}^{n} C(r+i, r) = C(r+n+1, r+1)` (∅-axiom)

Also called the *Christmas-stocking* or *hockey-stick* identity: summing a diagonal of Pascal's
triangle gives the next entry one row down and one column over.  A clean induction on `n` using
only Pascal's recurrence (`choose_succ_succ`) and `choose_self`.  The companion *column-sum* form
`Σ_{i=0}^{n} C(i, r) = C(n+1, r+1)` is the same identity reindexed.  All ∅-axiom.
-/

namespace E213.Lib.Math.Combinatorics.HockeyStick

open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Binomial (choose choose_succ_succ choose_self)
open E213.Lib.Math.NumberTheory.DyadicFSM.FLT.Sum (sumTo sumTo_succ)

/-- ★★★ **Hockey-stick identity** (diagonal form):
    `Σ_{i=0}^{n} C(r+i, r) = C(r+n+1, r+1)`.

    Induction on `n`: the base is `C(r,r) = C(r+1,r+1) = 1`; the step adds `C(r+n+1, r)` to the
    IH `C(r+n+1, r+1)` and recombines via Pascal `C(r+n+2, r+1) = C(r+n+1, r) + C(r+n+1, r+1)`. -/
theorem hockey_stick (r : Nat) : ∀ n,
    sumTo (n + 1) (fun i => choose (r + i) r) = choose (r + n + 1) (r + 1)
  | 0 => by
    show sumTo 1 (fun i => choose (r + i) r) = choose (r + 0 + 1) (r + 1)
    show sumTo 0 (fun i => choose (r + i) r) + choose (r + 0) r = choose (r + 0 + 1) (r + 1)
    show (0 : Nat) + choose (r + 0) r = choose (r + 0 + 1) (r + 1)
    rw [Nat.zero_add, Nat.add_zero, choose_self, choose_self]
  | n + 1 => by
    rw [sumTo_succ, hockey_stick r n]
    -- `C(r+n+1, r+1) + C(r+n+1, r) = C(r+n+2, r+1)` via Pascal
    show choose (r + n + 1) (r + 1) + choose (r + n + 1) r = choose (r + n + 1 + 1) (r + 1)
    rw [choose_succ_succ (r + n + 1) r]
    exact Nat.add_comm _ _

/-- ★★★ **Hockey-stick identity** (column form): `Σ_{i=0}^{n} C(i, r) = C(n+1, r+1)`.
    Terms with `i < r` vanish (`choose_eq_zero_of_lt`), so this is the diagonal form reindexed;
    here proved directly by the same Pascal induction, valid for all `n`. -/
theorem hockey_stick_column (r : Nat) : ∀ n,
    sumTo (n + 1) (fun i => choose i (r + 1)) = choose (n + 1) (r + 2)
  | 0 => by
    show sumTo 1 (fun i => choose i (r + 1)) = choose 1 (r + 2)
    show (0 : Nat) + choose 0 (r + 1) = choose 1 (r + 2)
    rfl
  | n + 1 => by
    rw [sumTo_succ, hockey_stick_column r n]
    -- `C(n+1, r+2) + C(n+1, r+1) = C(n+2, r+2)`
    show choose (n + 1) (r + 2) + choose (n + 1) (r + 1) = choose (n + 1 + 1) (r + 2)
    rw [choose_succ_succ (n + 1) (r + 1)]
    exact Nat.add_comm _ _

/-- Smoke: `C(2,2)+C(3,2)+C(4,2)+C(5,2) = 1+3+6+10 = 20 = C(6,3)`. -/
theorem hockey_stick_smoke :
    sumTo 4 (fun i => choose (2 + i) 2) = choose 6 3 := by decide

end E213.Lib.Math.Combinatorics.HockeyStick
