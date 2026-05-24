/-!
# Nat.beq cancellation helpers

Pure (∅-axiom) proofs of `Nat.beq` cancellation lemmas needed for
symbolic offset reductions in parametric cohomology proofs.

  · `nat_beq_refl' : Nat.beq n n = true` — pure structural recursion
  · `nat_beq_add_left : Nat.beq (a + b) (a + c) = Nat.beq b c` —
    left-cancellation via induction on `a`

These bridge abstract-`m` offsets (`9·m.val + k`) into
layer-independent `Nat.beq` comparisons, unlocking the arbitrary-`m`
parametric kill lemmas in `V33EnrichedParametric`.
-/

namespace E213.Lib.Math.Cohomology.NatBeqHelpers

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

end E213.Lib.Math.Cohomology.NatBeqHelpers
