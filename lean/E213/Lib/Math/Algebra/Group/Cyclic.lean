import E213.Meta.Nat.AddMod213

/-!
# Group Theory 213 — Cyclic group ℤ/nℤ (atomic, Nat-modular)

213-native paradigm: a *cyclic group* of order `n` is just `Nat`
with addition modulo `n`.  No abstract `Group` structure needed —
every property is a `Nat`-arithmetic identity.

Atomic content:
  * `cyclicAdd n a b := (a + b) % n`
  * Identity: `cyclicAdd n 0 a = a % n`.
  * Closure: result `< n` (when `n > 0`).
  * Specific small-`n` cases (n = 2..5).
-/

namespace E213.Lib.Math.Algebra.Group.Cyclic

/-- Cyclic addition. -/
def cyclicAdd (n a b : Nat) : Nat := (a + b) % n

/-- ★ Identity (left): `0 +_n a = a % n`. -/
theorem cyclicAdd_zero_left (n a : Nat) :
    cyclicAdd n 0 a = a % n := by
  show (0 + a) % n = a % n
  rw [Nat.zero_add]

/-- ★ Closure: result is `< n` when `n > 0`. -/
theorem cyclicAdd_lt (n a b : Nat) (h : 0 < n) :
    cyclicAdd n a b < n := Nat.mod_lt (a + b) h

/-- ★ ℤ/2ℤ: 1 + 1 = 0. -/
theorem z2_one_plus_one : cyclicAdd 2 1 1 = 0 := rfl

/-- ★ ℤ/5ℤ: 3 + 4 = 2. -/
theorem z5_three_plus_four : cyclicAdd 5 3 4 = 2 := rfl

/-- ★ ℤ/5ℤ: addition is commutative (term-mode `Nat.add_comm`). -/
theorem cyclicAdd_comm (n a b : Nat) :
    cyclicAdd n a b = cyclicAdd n b a := by
  show (a + b) % n = (b + a) % n
  rw [Nat.add_comm a b]


/-- ★ **`cyclicAdd` is associative**: `(a +ₙ b) +ₙ c = a +ₙ (b +ₙ c)`, both `(a+b+c) % n`.
    With `cyclicAdd_zero_left` and `cyclicAdd_comm`, `(ℤ/n, +ₙ)` is a commutative monoid. -/
theorem cyclicAdd_assoc (n a b c : Nat) :
    cyclicAdd n (cyclicAdd n a b) c = cyclicAdd n a (cyclicAdd n b c) := by
  show ((a + b) % n + c) % n = (a + (b + c) % n) % n
  rw [E213.Meta.Nat.AddMod213.add_mod_gen ((a + b) % n) c n,
      E213.Meta.Nat.AddMod213.add_mod_gen a ((b + c) % n) n,
      E213.Meta.Nat.AddMod213.mod_mod, E213.Meta.Nat.AddMod213.mod_mod,
      ← E213.Meta.Nat.AddMod213.add_mod_gen (a + b) c n,
      ← E213.Meta.Nat.AddMod213.add_mod_gen a (b + c) n,
      Nat.add_assoc]
end E213.Lib.Math.Algebra.Group.Cyclic
