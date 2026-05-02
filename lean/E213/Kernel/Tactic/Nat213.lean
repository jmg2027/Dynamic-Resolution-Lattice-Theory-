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

/-- `n < 4 → n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3`.  ∅-axiom. -/
theorem cases_lt_four {n : Nat} (h : n < 4) :
    n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 :=
  match Nat.lt_or_ge n 3 with
  | Or.inl hlt => (cases_lt_three hlt).imp id (·.imp id Or.inl)
  | Or.inr hge =>
    Or.inr (Or.inr (Or.inr (Nat.le_antisymm (Nat.le_of_lt_succ h) hge)))

/-- `n < 5 → n ∈ {0,1,2,3,4}`.  ∅-axiom — used for `Fin 5` decomposition
    in the cohomology cochain `pattern_eq_at` chain (Universal.Prop51). -/
theorem cases_lt_five {n : Nat} (h : n < 5) :
    n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 :=
  match Nat.lt_or_ge n 4 with
  | Or.inl hlt => (cases_lt_four hlt).imp id (·.imp id (·.imp id Or.inl))
  | Or.inr hge =>
    Or.inr (Or.inr (Or.inr (Or.inr
      (Nat.le_antisymm (Nat.le_of_lt_succ h) hge))))

/-- `n < 10 → n ∈ {0,…,9}`.  ∅-axiom — used for `Fin 10` decomposition
    (Cochain 5 2/3 = Fin (binom 5 2/3) → Bool) in Universal.Prop52/53. -/
theorem cases_lt_ten {n : Nat} (h : n < 10) :
    n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4
    ∨ n = 5 ∨ n = 6 ∨ n = 7 ∨ n = 8 ∨ n = 9 :=
  match Nat.lt_or_ge n 5 with
  | Or.inl hlt => (cases_lt_five hlt).imp id (·.imp id (·.imp id (·.imp id Or.inl)))
  | Or.inr hge =>
    -- 5 ≤ n < 10
    match Nat.lt_or_ge n 9 with
    | Or.inl hlt9 =>
      match Nat.lt_or_ge n 8 with
      | Or.inl hlt8 =>
        match Nat.lt_or_ge n 7 with
        | Or.inl hlt7 =>
          match Nat.lt_or_ge n 6 with
          | Or.inl hlt6 =>
            -- n = 5
            Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
              (Nat.le_antisymm (Nat.le_of_lt_succ hlt6) hge))))))
          | Or.inr hge6 =>
            -- n = 6
            Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
              (Nat.le_antisymm (Nat.le_of_lt_succ hlt7) hge6)))))))
        | Or.inr hge7 =>
          -- n = 7
          Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
            (Nat.le_antisymm (Nat.le_of_lt_succ hlt8) hge7))))))))
      | Or.inr hge8 =>
        -- n = 8
        Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          (Nat.le_antisymm (Nat.le_of_lt_succ hlt9) hge8)))))))))
    | Or.inr hge9 =>
      -- n = 9
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
        (Nat.le_antisymm (Nat.le_of_lt_succ h) hge9)))))))))

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

/-- `a * (b * c) = b * (a * c)`.  ∅-axiom replacement for
    `Nat.mul_left_comm` (Lean-core proof brings propext).  Term-mode
    via `mul_assoc` + `Nat.mul_comm` + `Eq.subst` only. -/
theorem mul_left_comm (a b c : Nat) : a * (b * c) = b * (a * c) :=
  let s1 : a * (b * c) = a * b * c := (mul_assoc a b c).symm
  let s2 : a * b * c = b * a * c :=
    (Nat.mul_comm a b) ▸ (rfl : a * b * c = a * b * c)
  let s3 : b * a * c = b * (a * c) := mul_assoc b a c
  s1.trans (s2.trans s3)

/-! ### Multiplicative cancellation + distributivity -/

/-- Right-cancellation under positive multiplier (Lean-core has only
    the left form `Nat.le_of_mul_le_mul_left`).  ∅-axiom via comm. -/
theorem le_of_mul_le_mul_right {a b c : Nat} (hc : 1 ≤ c)
    (h : a * c ≤ b * c) : a ≤ b :=
  Nat.le_of_mul_le_mul_left
    ((Nat.mul_comm a c).symm ▸ (Nat.mul_comm b c).symm ▸ h) hc

/-- `b ≤ a → c * (a - b) = c*a - c*b`.  ∅-axiom. -/
theorem mul_sub_distrib {a b c : Nat} (h : b ≤ a) :
    c * (a - b) = c * a - c * b := by
  have he : (a - b) + b = a := sub_add_cancel h
  have h1 : c * ((a - b) + b) = c * (a - b) + c * b := Nat.mul_add c (a - b) b
  have h2 : c * ((a - b) + b) = c * a := congrArg (c * ·) he
  have hcdist : c * a = c * (a - b) + c * b := h2.symm.trans h1
  have hcancel : c * (a - b) + c * b - c * b = c * (a - b) :=
    add_sub_cancel_right (c * (a - b)) (c * b)
  exact hcancel.symm.trans (congrArg (· - c * b) hcdist.symm)

-- NOTE: cohomological-trajectory primitives (parity, mod3, mod6,
-- CRT pairing) live in `Kernel/Tactic/Mod213.lean`.  They are
-- conceptually a *different layer* from this file — Mod213 is the
-- mod-cycle vocabulary, Nat213 is plain Nat-arithmetic helpers.
--
-- TODO: div / mod helpers.  `Nat.div_mul_le_self`, `Nat.div_add_mod`
-- all bring `propext`.  Need ∅-axiom division algorithm.

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
