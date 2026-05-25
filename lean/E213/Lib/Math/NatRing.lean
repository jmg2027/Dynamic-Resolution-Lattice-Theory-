/-!
# E213.Lib.Math.NatRing — PURE Nat ring infrastructure

The Lean 4 core proofs of `Nat.mul_assoc`, `Nat.add_mul`, and
`Nat.add_right_cancel` leak `propext` (through internal use of
`Nat.rec`-based proof skeletons that go through propositional
equality reflection).  This file re-derives the same identities
**PURELY** (∅-axiom) via direct structural recursion, providing a
Nat-side ring toolkit suitable for 213's strict-PURE standard.

## Re-derived PURE lemmas

  · `nat_mul_assoc : a * b * c = a * (b * c)`
  · `nat_add_mul  : (a + b) * c = a * c + b * c`
  · `nat_add_right_cancel : a + b = c + b → a = c`
  · `nat_add_left_cancel  : a + b = a + c → b = c`

Each is `#print axioms`-empty — verified PURE.

## Use case

The P-orbit closure marathon's `CassiniInduction` proves the
Cassini identity at concrete n = 0..9 by `decide`, but the
universal `∀n` lift requires Int polynomial manipulation
unavailable in PURE Lean (Int.add_comm, Int.mul_comm, etc. all
leak propext through Lean core).

The Nat-additive reformulation
  `L(n) · L(n+2) = L(n+1)² + d` (no subtraction)
sidesteps Int and enables universal ∀n via the PURE Nat ring
toolkit here.

All declarations PURE (∅-axiom).
-/

namespace E213.Lib.Math.NatRing

/-! ## §1 — PURE multiplication associativity -/

/-- `a * b * c = a * (b * c)` for Nat — PURE re-derivation by
    induction on `c`.  Core's `Nat.mul_assoc` leaks `propext`. -/
theorem nat_mul_assoc : ∀ (a b c : Nat), a * b * c = a * (b * c)
  | _, _, 0     => by rw [Nat.mul_zero, Nat.mul_zero, Nat.mul_zero]
  | a, b, c + 1 => by
      rw [Nat.mul_succ, Nat.mul_succ, Nat.mul_add, nat_mul_assoc a b c]

/-! ## §2 — PURE additive-multiplicative distribution -/

/-- `(a + b) * c = a * c + b * c` for Nat — PURE derivation via
    `Nat.mul_comm` (PURE) + `Nat.mul_add` (PURE).  Core's
    `Nat.add_mul` leaks `propext`. -/
theorem nat_add_mul (a b c : Nat) : (a + b) * c = a * c + b * c := by
  rw [Nat.mul_comm (a + b) c, Nat.mul_add, Nat.mul_comm c a, Nat.mul_comm c b]

/-! ## §3 — PURE Nat additive cancellation -/

/-- `a + b = c + b → a = c` — PURE via induction on `b` using
    `Nat.succ.inj` (PURE).  Core's `Nat.add_right_cancel` leaks
    `propext`. -/
theorem nat_add_right_cancel : ∀ {a b c : Nat}, a + b = c + b → a = c
  | _, 0,     _, h => h
  | _, _ + 1, _, h => nat_add_right_cancel (Nat.succ.inj h)

/-- `a + b = a + c → b = c` — derived from right cancellation
    via `Nat.add_comm` (PURE). -/
theorem nat_add_left_cancel {a b c : Nat} (h : a + b = a + c) : b = c := by
  apply nat_add_right_cancel (b := a)
  rw [Nat.add_comm b a, Nat.add_comm c a]
  exact h

/-! ## §4 — PURE Nat sub-add cancellation -/

/-- `b ≤ a → a - b + b = a` — PURE re-derivation via direct
    recursion on `b` with `Nat.succ_sub_succ` (PURE).  Core's
    `Nat.sub_add_cancel` leaks `propext`. -/
theorem nat_sub_add_cancel : ∀ {a b : Nat}, b ≤ a → a - b + b = a
  | _, 0,     _ => by rw [Nat.sub_zero, Nat.add_zero]
  | 0, _ + 1, h => absurd h (by intro hf; cases hf)
  | a + 1, b + 1, h => by
    have hb : b ≤ a := Nat.le_of_succ_le_succ h
    have ih := nat_sub_add_cancel hb
    rw [Nat.succ_sub_succ, Nat.add_succ, ih]

/-! ## §5 — Convenience: `a + b - b = a` -/

/-- `a + b - b = a` — PURE derivation from `nat_sub_add_cancel`
    and `Nat.add_sub_cancel`. -/
theorem nat_add_sub_self_right (a b : Nat) : a + b - b = a := by
  induction b with
  | zero => rw [Nat.add_zero, Nat.sub_zero]
  | succ k ih => rw [Nat.add_succ, Nat.succ_sub_succ, ih]

/-! ## §6 — Inequality cancellation -/

/-- `a + b ≤ c + b → a ≤ c` — PURE re-derivation by induction on
    `b` using `Nat.le_of_succ_le_succ` (PURE).  Core's
    `Nat.le_of_add_le_add_right` leaks `propext`. -/
theorem nat_le_of_add_le_add_right :
    ∀ {a b c : Nat}, a + b ≤ c + b → a ≤ c
  | _, 0,     _, h => by rw [Nat.add_zero, Nat.add_zero] at h; exact h
  | _, _ + 1, _, h => nat_le_of_add_le_add_right (Nat.le_of_succ_le_succ h)

/-! ## §7 — Helpful re-arrangement: `a · (b · c) = b · a · c` -/

/-- `a * (b * c) = b * a * c` for Nat — PURE via `nat_mul_assoc` +
    `Nat.mul_comm` (both PURE). -/
theorem nat_swap_left_mul (a b c : Nat) : a * (b * c) = b * a * c := by
  rw [← nat_mul_assoc, Nat.mul_comm a b]

/-! ## §8 — Small-coefficient expansions -/

/-- `3 * x = x + x + x` for Nat — useful for Pell-Lucas arithmetic
    where `NS = 3`.  PURE via `nat_add_mul` chain. -/
theorem three_mul_eq (x : Nat) : 3 * x = x + x + x := by
  rw [show (3 : Nat) = 1 + 1 + 1 from rfl, nat_add_mul, nat_add_mul,
      Nat.one_mul]

/-- `2 * x = x + x` for Nat. -/
theorem two_mul_eq (x : Nat) : 2 * x = x + x := by
  rw [show (2 : Nat) = 1 + 1 from rfl, nat_add_mul, Nat.one_mul]

end E213.Lib.Math.NatRing
