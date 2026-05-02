/-!
# 213-native `Nat` helpers (∅-axiom)

Replacements for Lean-core `Nat.*` lemmas that bring `propext` (or
`Quot.sound`) into downstream theorems.  Every theorem here is
verified `#print axioms` ∅.

Companion to `Omega213.lean` (linear arithmetic tactic) and
`Fin213.lean` (Fin-construction helpers).  See
`AXIOM_FREE_STATUS.md` for migration methodology.

The Lean-core lemmas these replace are listed beside each.
-/

namespace E213.Tactic.Nat213

/-- `Nat.sub_add_cancel` at `b = 1`.

    Lean-core `Nat.sub_add_cancel` is proved with `simp`, which
    inserts `propext`.  This direct cases-on-`n` proof is ∅-axiom. -/
theorem sub_one_add_one {n : Nat} (h : n ≠ 0) : n - 1 + 1 = n := by
  cases n with
  | zero => exact absurd rfl h
  | succ k => rfl

/-- General `Nat.sub_add_cancel`: `m ≤ n → n - m + m = n`.  ∅-axiom
    via direct recursion on `m`. -/
theorem sub_add_cancel : ∀ {n m : Nat}, m ≤ n → n - m + m = n
  | _, 0, _ => rfl
  | 0, _+1, h => absurd h (Nat.not_succ_le_zero _)
  | n+1, m+1, h =>
    let hk : m ≤ n := Nat.le_of_succ_le_succ h
    let ih : n - m + m = n := sub_add_cancel hk
    let ih' : (n - m) + (m + 1) = n + 1 := congrArg (·+1) ih
    let step : (n + 1) - (m + 1) = n - m := Nat.succ_sub_succ_eq_sub n m
    step.symm ▸ ih'

/-- Symmetric form: `m ≤ n → m + (n - m) = n`.  ∅-axiom. -/
theorem add_sub_of_le {n m : Nat} (h : m ≤ n) : m + (n - m) = n := by
  have : n - m + m = n := sub_add_cancel h
  have hcomm : m + (n - m) = (n - m) + m := Nat.add_comm m (n - m)
  exact hcomm.trans this

/-- `(a + b) - b = a`.  ∅-axiom replacement (Lean-core
    `Nat.add_sub_cancel` proof brings propext on some forms). -/
theorem add_sub_cancel_right : ∀ (a b : Nat), a + b - b = a
  | _, 0 => rfl
  | a, b+1 =>
    let step : (a + b + 1) - (b + 1) = (a + b) - b := Nat.succ_sub_succ_eq_sub _ _
    let ih : (a + b) - b = a := add_sub_cancel_right a b
    step.trans ih

/-- `a + b ≤ c → a ≤ c - b`.  ∅-axiom replacement. -/
theorem le_sub_of_add_le {a b c : Nat} (h : a + b ≤ c) : a ≤ c - b :=
  let h1 : (a + b) - b ≤ c - b := Nat.sub_le_sub_right h b
  let h2 : (a + b) - b = a := add_sub_cancel_right a b
  h2 ▸ h1

/-- `n < 2 → n = 0 ∨ n = 1`.  ∅-axiom. -/
theorem cases_lt_two {n : Nat} (h : n < 2) : n = 0 ∨ n = 1 :=
  match Nat.lt_or_ge n 1 with
  | Or.inl hlt =>
    Or.inl (Nat.le_antisymm (Nat.le_of_lt_succ hlt) (Nat.zero_le _))
  | Or.inr hge =>
    Or.inr (Nat.le_antisymm (Nat.le_of_lt_succ h) hge)

/-- `n < 3 → n = 0 ∨ n = 1 ∨ n = 2`.  ∅-axiom. -/
theorem cases_lt_three {n : Nat} (h : n < 3) :
    n = 0 ∨ n = 1 ∨ n = 2 :=
  match Nat.lt_or_ge n 2 with
  | Or.inl hlt => (cases_lt_two hlt).imp id Or.inl
  | Or.inr hge =>
    Or.inr (Or.inr (Nat.le_antisymm (Nat.le_of_lt_succ h) hge))

/-- `a + c = b + c → a = b`.  ∅-axiom (Lean-core brings propext). -/
theorem add_right_cancel : ∀ {a b c : Nat}, a + c = b + c → a = b
  | _, _, 0, h => h
  | _, _, _+1, h => add_right_cancel (Nat.succ.inj h)

/-- `a + b = a + c → b = c`.  ∅-axiom. -/
theorem add_left_cancel {a b c : Nat} (h : a + b = a + c) : b = c :=
  let h' : b + a = c + a := (Nat.add_comm b a).trans (h.trans (Nat.add_comm a c))
  add_right_cancel h'

/-- `a * b * c = a * (b * c)`.  ∅-axiom replacement for
    `Nat.mul_assoc` (Lean-core proof brings propext). -/
theorem mul_assoc : ∀ (a b c : Nat), a * b * c = a * (b * c)
  | _, _, 0 => rfl
  | a, b, c+1 =>
    let ih : a * b * c = a * (b * c) := mul_assoc a b c
    let lhs_eq : a * b * c + a * b = a * (b * c) + a * b :=
      congrArg (· + a * b) ih
    lhs_eq.trans (Nat.mul_add a (b * c) b).symm

/-! ### Cohomological parity

Lean-core `Nat.mod` is well-founded; its reduction lemmas (e.g.
`Nat.add_mod_right`) bring `propext`.  213's view of mod-2 is
*how much a path hasn't completed a half-cycle* — a Bool invariant
defined by direct step-2 recursion.  All theorems below are
∅-axiom by structural reduction. -/

/-- 213-native parity: cohomological "uncompleted half-cycle" invariant. -/
def parity : Nat → Bool
  | 0     => false
  | 1     => true
  | n + 2 => parity n

@[simp] theorem parity_step (n : Nat) : parity (n + 2) = parity n := rfl
@[simp] theorem parity_zero : parity 0 = false := rfl
@[simp] theorem parity_one : parity 1 = true := rfl

theorem parity_succ : ∀ n, parity (n + 1) = !parity n
  | 0     => rfl
  | 1     => rfl
  | n + 2 => parity_succ n

theorem parity_double : ∀ n, parity (2 * n) = false
  | 0     => rfl
  | n + 1 => parity_double n

theorem parity_double_succ : ∀ n, parity (2 * n + 1) = true
  | 0     => rfl
  | n + 1 => parity_double_succ n

/-- `b ≤ a → c * (a - b) = c*a - c*b`.  ∅-axiom. -/
theorem mul_sub_distrib {a b c : Nat} (h : b ≤ a) :
    c * (a - b) = c * a - c * b := by
  have he : (a - b) + b = a := sub_add_cancel h
  have h1 : c * ((a - b) + b) = c * (a - b) + c * b := Nat.mul_add c (a - b) b
  have h2 : c * ((a - b) + b) = c * a := congrArg (c * ·) he
  -- From h1: c * a = c * (a-b) + c*b after substituting via h2.symm
  have hcdist : c * a = c * (a - b) + c * b := h2.symm.trans h1
  -- c * (a - b) = c * (a - b) + c * b - c * b
  have hcancel : c * (a - b) + c * b - c * b = c * (a - b) :=
    add_sub_cancel_right (c * (a - b)) (c * b)
  -- = c * a - c * b
  exact hcancel.symm.trans (congrArg (· - c * b) hcdist.symm)

-- TODO: div / mod helpers.  `Nat.div_mul_le_self`, `Nat.div_add_mod`,
-- `Nat.mod_add_div` all bring `propext` from Lean-core proofs, blocking
-- ∅-axiom div_lt_of_lt_mul / le_div_of_mul_le.  Need to reprove the
-- division-algorithm identity ∅-axiom via recursion, then derive the
-- bounds.

/-- From `b ≤ a` and `a ≠ b` deduce `a ≠ 0`. -/
theorem ne_zero_of_le_ne {a b : Nat}
    (hge : b ≤ a) (hne : a ≠ b) : a ≠ 0 := by
  intro h0
  have hlt : b < a := Nat.lt_of_le_of_ne hge (Ne.symm hne)
  exact Nat.not_lt_zero _ (h0 ▸ hlt)

/-- From `b ≤ a`, `a ≠ b`, and `a < n + 1`, deduce `a - 1 < n`. -/
theorem sub_one_lt_of_lt_succ_ne {a b n : Nat}
    (hge : b ≤ a) (hne : a ≠ b) (hlt : a < n + 1) : a - 1 < n := by
  have hpos : a ≠ 0 := ne_zero_of_le_ne hge hne
  have hsub : a - 1 < a := Nat.sub_one_lt hpos
  exact Nat.lt_of_lt_of_le hsub (Nat.le_of_lt_succ hlt)

end E213.Tactic.Nat213
