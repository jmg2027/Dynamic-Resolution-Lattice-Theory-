/-!
# Nat.beq cancellation helpers

Pure (∅-axiom) proofs of `Nat.beq` cancellation lemmas needed for
symbolic offset reductions in parametric cohomology proofs.

  · `nat_beq_refl' : Nat.beq n n = true` — pure structural recursion
  · `nat_beq_add_left : Nat.beq (a + b) (a + c) = Nat.beq b c` —
    left-cancellation via induction on `a`
  · `nat_beq_eq_false_of_ne : n ≠ m → Nat.beq n m = false` —
    contrapositive of `Nat.eq_of_beq_eq_true`
  · `nat_beq_false_of_lt : n < m → Nat.beq n m = false`
  · `nine_block_disjoint` — `Nat.beq (9·a + r₁) (9·b + r₂) = false`
    when `a ≠ b`, `r₁ < 9`, `r₂ < 9` (the "9-block disjoint" fact
    needed for cross-layer vanishing in K_{3,3}^{(c)})

These bridge abstract-`m` offsets (`9·m.val + k`) into
layer-independent `Nat.beq` comparisons, unlocking the arbitrary-`m`
parametric kill lemmas in `V33EnrichedParametric` and the
cross-layer vanishing in `V33EnrichedParametricDualSpan`.
-/

namespace E213.Lib.Math.Cohomology.Infrastructure.NatBeqHelpers

/-- `Nat.beq n n = true` by structural recursion on `n`. -/
theorem nat_beq_refl' : ∀ (n : Nat), Nat.beq n n = true
  | 0 => rfl
  | n+1 => nat_beq_refl' n

/-- `Nat.succ_add`: `(k+1) + b = (k + b) + 1`.  Lean core lemma. -/
theorem nat_succ_add : ∀ (k b : Nat), (k + 1) + b = (k + b) + 1
  | _, 0 => rfl
  | k, b+1 => congrArg (· + 1) (nat_succ_add k b)

/-- `Nat.beq` left-cancellation: `Nat.beq (a + b) (a + c) = Nat.beq b c`. -/
theorem nat_beq_add_left : ∀ (a b c : Nat),
    Nat.beq (a + b) (a + c) = Nat.beq b c
  | 0, b, c => by
    show Nat.beq (0 + b) (0 + c) = Nat.beq b c
    rw [Nat.zero_add b, Nat.zero_add c]
  | a+1, b, c => by
    rw [nat_succ_add a b, nat_succ_add a c]
    show Nat.beq ((a + b) + 1) ((a + c) + 1) = Nat.beq b c
    show Nat.beq (a + b) (a + c) = Nat.beq b c
    exact nat_beq_add_left a b c

/-- `Nat.beq n m = false` when `n ≠ m`.  Contrapositive of
    `Nat.eq_of_beq_eq_true` (Lean core). -/
theorem nat_beq_eq_false_of_ne {n m : Nat} (h : n ≠ m) : Nat.beq n m = false := by
  cases hbeq : Nat.beq n m with
  | true => exact absurd (Nat.eq_of_beq_eq_true hbeq) h
  | false => rfl

/-- `Nat.beq n m = false` when `n < m`. -/
theorem nat_beq_false_of_lt {n m : Nat} (h : n < m) : Nat.beq n m = false :=
  nat_beq_eq_false_of_ne (Nat.ne_of_lt h)

/-- 9-block disjointness: when `a ≠ b` and `r₁, r₂ < 9`, the offsets
    `9·a + r₁` and `9·b + r₂` lie in disjoint blocks of size 9, hence
    are unequal.  Used to derive cross-layer cup vanishing at
    K_{3,3}^{(c)} (where each layer occupies a `[9m, 9m + 9)`
    contiguous range of edge indices). -/
theorem nine_block_disjoint {a b r1 r2 : Nat}
    (h_ab : a ≠ b) (h1 : r1 < 9) (h2 : r2 < 9) :
    Nat.beq (9 * a + r1) (9 * b + r2) = false := by
  cases Nat.lt_or_ge a b with
  | inl h_lt =>
      apply nat_beq_false_of_lt
      calc 9 * a + r1 < 9 * a + 9         := Nat.add_lt_add_left h1 (9 * a)
        _             = 9 * (a + 1)        := (Nat.mul_succ 9 a).symm
        _             ≤ 9 * b              := Nat.mul_le_mul_left 9 h_lt
        _             ≤ 9 * b + r2         := Nat.le_add_right _ _
  | inr h_ge =>
      have h_gt : b < a := Nat.lt_of_le_of_ne h_ge (Ne.symm h_ab)
      apply nat_beq_eq_false_of_ne
      intro heq
      have h_lt : 9 * b + r2 < 9 * a + r1 := by
        calc 9 * b + r2 < 9 * b + 9         := Nat.add_lt_add_left h2 (9 * b)
          _             = 9 * (b + 1)        := (Nat.mul_succ 9 b).symm
          _             ≤ 9 * a              := Nat.mul_le_mul_left 9 h_gt
          _             ≤ 9 * a + r1         := Nat.le_add_right _ _
      exact Nat.ne_of_lt h_lt heq.symm

/-- `==`-form variant: `(a == b) = false` when `a ≠ b` (via the
    `Decidable` instance for Nat).  Bridges between `Nat.beq` and the
    `==` operator that appears in definitions like `starS` / `incidT`. -/
theorem nat_beq_op_eq_false_of_ne {a b : Nat} (h : a ≠ b) : (a == b) = false := by
  show decide (a = b) = false
  exact decide_eq_false h

/-- `==`-form variant of `nine_block_disjoint`. -/
theorem nine_block_disjoint_op {a b r1 r2 : Nat}
    (h_ab : a ≠ b) (h1 : r1 < 9) (h2 : r2 < 9) :
    ((9 * a + r1) == (9 * b + r2)) = false := by
  apply nat_beq_op_eq_false_of_ne
  intro heq
  have : Nat.beq (9 * a + r1) (9 * b + r2) = true := by
    rw [heq]; exact nat_beq_refl' _
  rw [nine_block_disjoint h_ab h1 h2] at this
  exact Bool.noConfusion this

end E213.Lib.Math.Cohomology.Infrastructure.NatBeqHelpers
