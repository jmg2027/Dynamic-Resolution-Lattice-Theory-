import E213.Lib.Math.UniverseChain.Atomicity

/-!
# Step 2 — The unique alive decomposition: 5 = 2·1 + 3·1 (∅-axiom)

Step 1 says size 5 is forced.  This step records *the shape* of
the unique alive decomposition: `(a, b) = (1, 1)`, so

    5 = 2 · 1 + 3 · 1 = 2 + 3.

Two atoms — `2` and `3` — appear with coefficient `1` each.  No
extra factor on either side; the decomposition splits 5 into
exactly two non-trivial pieces of sizes 2 and 3.

The 213-native consequence: any quantity forced to be size 5
carries an *intrinsic* (2, 3) labelling — these are not external
labels, they are the unique alive decomposition itself.

All facts here are `rfl` or follow from `canonical_partition` in
`Theory.Atomicity.Five`.
-/

namespace E213.Lib.Math.UniverseChain.Decomposition

open E213.Lib.Math.UniverseChain.Atomicity (Decomp IsAlive)

/-- ★ The (1, 1) decomposition of 5. -/
theorem five_eq_2_plus_3 : (5 : Nat) = 2 * 1 + 3 * 1 := rfl

/-- ★ Equivalent flat form: `5 = 2 + 3`. -/
theorem five_eq_two_plus_three : (5 : Nat) = 2 + 3 := rfl

/-- ★ The (1, 1) decomposition is itself a `Decomp 5`. -/
theorem decomp_five_one_one : Decomp 5 1 1 := rfl

/-- ★ The (1, 1) decomposition is alive. -/
theorem one_one_alive : IsAlive 1 1 := ⟨rfl, rfl⟩

/-- ★ Uniqueness of the alive decomposition: if `Decomp 5 a b`
    holds and is alive, then `(a, b) = (1, 1)`. -/
theorem unique_alive_decomp (a b : Nat)
    (h : Decomp 5 a b ∧ IsAlive a b) : a = 1 ∧ b = 1 :=
  E213.Theory.Atomicity.Five.canonical_partition a b h

/-- ★★ The decomposition is a 2-element partition: a "2-piece"
    (coefficient of atom 2) and a "3-piece" (coefficient of
    atom 3), each contributing exactly one unit. -/
theorem two_piece_three_piece :
    (5 : Nat) = 2 * 1 + 3 * 1
    ∧ Decomp 5 1 1
    ∧ IsAlive 1 1
    ∧ ∀ a b, Decomp 5 a b ∧ IsAlive a b → a = 1 ∧ b = 1 :=
  ⟨rfl, rfl, ⟨rfl, rfl⟩, unique_alive_decomp⟩

end E213.Lib.Math.UniverseChain.Decomposition
