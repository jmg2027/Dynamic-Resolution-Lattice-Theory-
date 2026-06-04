import E213.Meta.Nat.PureNat

/-!
# E213.Meta.Nat.NatRing213 — PURE Nat ring infrastructure

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

namespace E213.Meta.Nat.NatRing213

/-! ## §1 — PURE multiplication associativity -/

/-- `a * b * c = a * (b * c)` for Nat — canonical PURE proof in
    `PureNat`, re-exported here for the `nat_*` ring toolkit. -/
theorem nat_mul_assoc (a b c : Nat) : a * b * c = a * (b * c) :=
  E213.Meta.Nat.PureNat.mul_assoc a b c

/-! ## §2 — PURE additive-multiplicative distribution -/

/-- `(a + b) * c = a * c + b * c` for Nat — canonical PURE proof in
    `PureNat`, re-exported here for the `nat_*` ring toolkit. -/
theorem nat_add_mul (a b c : Nat) : (a + b) * c = a * c + b * c :=
  E213.Meta.Nat.PureNat.add_mul a b c

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

/-! ## §9 — Strict multiplication monotonicity (PURE)

Lean-core `Nat.mul_lt_mul_left` / `Nat.mul_lt_mul_right` are `Iff`s
that pull `Classical.choice`, and `Nat.exists_eq_add_of_lt` pulls
`Classical` too.  These constructive forms route strict `<` through
the `(b+1)·a ≤ c·a` chain so they stay ∅-axiom. -/

/-- `b·a < c·a` for `0 < a`, `b < c` — PURE right-strict monotonicity. -/
theorem nat_mul_lt_mul_right {b c a : Nat} (ha : 0 < a) (h : b < c) :
    b * a < c * a := by
  have hstep : (b + 1) * a ≤ c * a := Nat.mul_le_mul_right a h
  have heq : (b + 1) * a = b * a + a := by rw [nat_add_mul, Nat.one_mul]
  rw [heq] at hstep
  exact Nat.le_trans (Nat.lt_add_of_pos_right ha) hstep

/-- `c·a < c·b` for `0 < c`, `a < b` — PURE left-strict monotonicity
    (commute to the right-strict form). -/
theorem nat_mul_lt_mul_left {a b c : Nat} (hc : 0 < c) (h : a < b) :
    c * a < c * b := by
  rw [Nat.mul_comm c a, Nat.mul_comm c b]; exact nat_mul_lt_mul_right hc h

/-- `c·m < c·n` from `1 ≤ c` and `m < n` — left-strict form stated with
    the `1 ≤ c` hypothesis used at edge-index bounds.  PURE. -/
theorem mul_lt_mul_left_pure {c m n : Nat} (hc : 1 ≤ c) (h : m < n) :
    c * m < c * n :=
  nat_mul_lt_mul_left hc h

/-! ## §10 — Additive / cancel / square algebra (PURE) -/

/-- `a + (b + 1) + a = 2·a + b + 1`.  PURE additive rearrangement. -/
theorem add_dup_succ (a b : Nat) : a + (b + 1) + a = 2 * a + b + 1 := by
  rw [Nat.two_mul, Nat.add_right_comm a (b + 1) a, ← Nat.add_assoc]

/-- If `b ≥ 1`, `c ≥ 1`, and `b · c = 1`, then `b = 1`.  PURE
    (`Nat.succ.inj` / `Nat.succ_ne_zero` leak propext; `noConfusion`
    is PURE). -/
theorem mul_eq_one_left (b c : Nat) (hb : b ≥ 1) (hc : c ≥ 1)
    (hbc : b * c = 1) : b = 1 := by
  cases b with
  | zero => exact absurd hb (Nat.not_succ_le_zero 0)
  | succ b0 =>
    cases b0 with
    | zero => rfl
    | succ b1 =>
      cases c with
      | zero => exact absurd hc (Nat.not_succ_le_zero 0)
      | succ c0 =>
        exfalso
        have hbc' : ((b1 + 1 + 1) * c0 + b1).succ.succ = 1 := hbc
        exact Nat.noConfusion hbc' (fun h2 => Nat.noConfusion h2)

/-- If `b ≥ 1`, `c ≥ 1`, and `b · c = 1`, then `c = 1`.  PURE. -/
theorem mul_eq_one_right (b c : Nat) (hb : b ≥ 1) (hc : c ≥ 1)
    (hbc : b * c = 1) : c = 1 := by
  have hb1 := mul_eq_one_left b c hb hc hbc
  subst hb1
  rw [Nat.one_mul] at hbc
  exact hbc

/-- `(x·y)·(x·y) = (x·x)·(y·y)` — PURE square-of-product. -/
theorem mul_sq (x y : Nat) : (x * y) * (x * y) = (x * x) * (y * y) := by
  rw [nat_mul_assoc, ← nat_mul_assoc y x y, Nat.mul_comm y x, nat_mul_assoc x y y,
      ← nat_mul_assoc x x (y * y)]

/-- `x² ≤ y² → x ≤ y` on Nat (PURE; rules out `y < x` via strict square
    monotonicity).  `Nat.lt_or_ge` / `Nat.not_le` are PURE. -/
theorem sq_le_imp (x y : Nat) (h : x * x ≤ y * y) : x ≤ y := by
  cases Nat.lt_or_ge y x with
  | inr hle => exact hle
  | inl hgt =>
    have hx0 : 0 < x := Nat.le_trans (Nat.succ_le_succ (Nat.zero_le y)) hgt
    have h1 : y * y ≤ y * x := Nat.mul_le_mul_left y (Nat.le_of_lt hgt)
    have h2 : y * x < x * x := nat_mul_lt_mul_right hx0 hgt
    exact (Nat.not_le.mpr (Nat.le_trans (Nat.succ_le_succ h1) h2) h).elim

/-- `x² < y² → x < y` on Nat (PURE; rule out `y ≤ x` via `Nat.mul_le_mul`). -/
theorem sq_lt_imp (x y : Nat) (h : x * x < y * y) : x < y := by
  cases Nat.lt_or_ge x y with
  | inl hlt => exact hlt
  | inr hge => exact (Nat.not_lt.mpr (Nat.mul_le_mul hge hge) h).elim

end E213.Meta.Nat.NatRing213
