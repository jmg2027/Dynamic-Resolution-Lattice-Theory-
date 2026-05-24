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

/-! ## Reassoc-then-cancel variants

Patterns that arise in parametric `edge_idx`/`starS`/`incidT` reductions
where the offset shows up as `m + p + q` (left-associated) rather than
`m + (p + q)`.  Inlining a `Nat.add_assoc` rewrite before applying
`nat_beq_add_left` avoids ad-hoc `rw` placement (and the loops that
naive `Nat.add_assoc` rewriting causes). -/

/-- `Nat.beq (a + b + c) (a + d) = Nat.beq (b + c) d`. -/
theorem nat_beq_add_left_assoc1 (a b c d : Nat) :
    Nat.beq (a + b + c) (a + d) = Nat.beq (b + c) d := by
  rw [Nat.add_assoc a b c]
  exact nat_beq_add_left a (b + c) d

/-- `Nat.beq (a + b + c) (a + d + e) = Nat.beq (b + c) (d + e)`. -/
theorem nat_beq_add_left_assoc2 (a b c d e : Nat) :
    Nat.beq (a + b + c) (a + d + e) = Nat.beq (b + c) (d + e) := by
  rw [Nat.add_assoc a b c, Nat.add_assoc a d e]
  exact nat_beq_add_left a (b + c) (d + e)

/-! ## `==`/`decide`-flavoured cancellation

`(x == y)` for `Nat` is `decide (x = y)` (via the generic
`[DecidableEq α] ⇒ BEq α` instance), not `Nat.beq x y` directly.
The cancellation lemmas below operate on the `decide` surface form
that `starS`/`incidT` definitions actually emit, sidestepping the
`Nat.beq` ↔ `decide` symbol mismatch in `rw`-based tactics. -/

/-- Pure (∅-axiom) left-cancellation for `Nat`, replacing
    `Nat.add_left_cancel` which depends on `propext`. -/
theorem nat_add_left_cancel_pure : ∀ {a b c : Nat}, a + b = a + c → b = c
  | 0, b, c, h => by rw [Nat.zero_add, Nat.zero_add] at h; exact h
  | a+1, b, c, h => by
    rw [nat_succ_add a b, nat_succ_add a c] at h
    exact nat_add_left_cancel_pure (Nat.succ.inj h)

/-- `decide`/`==`-flavoured left-cancellation, propext-free. -/
theorem nat_decide_add_left (a b c : Nat) :
    (a + b == a + c) = (b == c) := by
  show decide (a + b = a + c) = decide (b = c)
  cases hbc : decide (b = c) with
  | true =>
    have : b = c := of_decide_eq_true hbc
    subst this
    exact decide_eq_true rfl
  | false =>
    have hne : ¬(b = c) := of_decide_eq_false hbc
    exact decide_eq_false (fun h => hne (nat_add_left_cancel_pure h))

/-- Reassoc + cancel: `(a + b + c == a + d) = (b + c == d)`. -/
theorem nat_decide_add_left_assoc1 (a b c d : Nat) :
    (a + b + c == a + d) = (b + c == d) := by
  rw [Nat.add_assoc a b c]
  exact nat_decide_add_left a (b + c) d

/-- Reassoc + cancel: `(a + b + c == a + d + e) = (b + c == d + e)`. -/
theorem nat_decide_add_left_assoc2 (a b c d e : Nat) :
    (a + b + c == a + d + e) = (b + c == d + e) := by
  rw [Nat.add_assoc a b c, Nat.add_assoc a d e]
  exact nat_decide_add_left a (b + c) (d + e)

end E213.Lib.Math.Cohomology.Infrastructure.NatBeqHelpers
