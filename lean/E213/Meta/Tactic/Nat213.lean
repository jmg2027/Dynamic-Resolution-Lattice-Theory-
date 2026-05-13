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

/-- `(k + n) - (k + m) = n - m`.  ∅-axiom replacement for
    `Nat.add_sub_add_left` (Lean-core proof brings propext).
    Term-mode via Nat.zero_add + Nat.succ_add + Nat.succ_sub_succ. -/
theorem add_sub_add_left : ∀ (k n m : Nat), (k + n) - (k + m) = n - m
  | 0, n, m =>
    let h1 : (0 + n) - (0 + m) = n - (0 + m) :=
      congrArg (fun x => x - (0 + m)) (Nat.zero_add n)
    let h2 : n - (0 + m) = n - m :=
      congrArg (fun x => n - x) (Nat.zero_add m)
    h1.trans h2
  | k+1, n, m =>
    let h1 : (k + 1) + n = (k + n) + 1 := Nat.succ_add k n
    let h2 : (k + 1) + m = (k + m) + 1 := Nat.succ_add k m
    let h3 : ((k + n) + 1) - ((k + m) + 1) = (k + n) - (k + m) :=
      Nat.succ_sub_succ_eq_sub (k + n) (k + m)
    let ih : (k + n) - (k + m) = n - m := add_sub_add_left k n m
    let step1 : (k + 1) + n - ((k + 1) + m) = ((k + n) + 1) - ((k + m) + 1) :=
      h2 ▸ h1 ▸ rfl
    step1.trans (h3.trans ih)

/-- `(a + k) - (b + k) = a - b`.  ∅-axiom — companion to
    `add_sub_add_left`, derived via `Nat.add_comm`. -/
theorem add_sub_add_right (a k b : Nat) : (a + k) - (b + k) = a - b :=
  let h1 : (a + k) - (b + k) = (k + a) - (k + b) :=
    (Nat.add_comm k b) ▸ (Nat.add_comm k a) ▸ rfl
  h1.trans (add_sub_add_left k a b)

/-- `(a + b) * c = a * c + b * c`.  ∅-axiom replacement for
    `Nat.add_mul` (Lean-core proof brings propext).  Term-mode
    via `Nat.mul_comm` + `Nat.mul_add`. -/
theorem add_mul (a b c : Nat) : (a + b) * c = a * c + b * c :=
  let h1 : (a + b) * c = c * (a + b) := Nat.mul_comm (a + b) c
  let h2 : c * (a + b) = c * a + c * b := Nat.mul_add c a b
  let h3 : c * a + c * b = a * c + b * c :=
    (Nat.mul_comm c a) ▸ (Nat.mul_comm c b) ▸ rfl
  h1.trans (h2.trans h3)

/-- `c ≤ b → a + b - c = a + (b - c)`.  ∅-axiom replacement for
    `Nat.add_sub_assoc` (Lean-core proof brings propext). -/
theorem add_sub_assoc :
    ∀ (a : Nat) {b c : Nat}, c ≤ b → a + b - c = a + (b - c)
  | _, _, 0, _ => rfl
  | a, b+1, c+1, h =>
    let h' : c ≤ b := Nat.le_of_succ_le_succ h
    let ih : a + b - c = a + (b - c) := add_sub_assoc a h'
    -- a + (b+1) - (c+1) = (a + b + 1) - (c+1) [Nat.add_succ]
    --                   = a + b - c [Nat.succ_sub_succ_eq_sub]
    --                   = a + (b - c) [ih]
    --                   = a + ((b+1) - (c+1)) [Nat.succ_sub_succ_eq_sub.symm]
    let step1 : a + (b + 1) = (a + b) + 1 := Nat.add_succ a b
    let step2 : (a + b + 1) - (c + 1) = (a + b) - c :=
      Nat.succ_sub_succ_eq_sub (a + b) c
    let step3 : (b + 1) - (c + 1) = b - c := Nat.succ_sub_succ_eq_sub b c
    let lhs : a + (b + 1) - (c + 1) = (a + b) - c := step1 ▸ step2
    let rhs : a + ((b + 1) - (c + 1)) = a + (b - c) := step3 ▸ rfl
    lhs.trans (ih.trans rhs.symm)
  | _, 0, _+1, h => absurd h (Nat.not_succ_le_zero _)

/-- `0 < b - a` from `a < b`.  ∅-axiom replacement for
    `Nat.sub_pos_of_lt` (Lean-core proof brings propext). -/
theorem sub_pos_of_lt {a b : Nat} (h : a < b) : 0 < b - a :=
  let step : (a + 1) - a ≤ b - a := Nat.sub_le_sub_right h a
  let comm_eq : a + 1 = 1 + a := Nat.add_comm a 1
  let cancel : 1 + a - a = 1 := add_sub_cancel_right 1 a
  -- `(a + 1) - a = 1`: combine via congrArg + cancel.
  let h_eq : (a + 1) - a = 1 :=
    (congrArg (· - a) comm_eq).trans cancel
  -- Substitute (a+1) - a → 1 in step: 1 ≤ b - a, i.e., 0 < b - a.
  Eq.subst (motive := fun x => x ≤ b - a) h_eq step

/-- `a + b ≤ a + c → b ≤ c`.  ∅-axiom replacement for
    `Nat.le_of_add_le_add_left` (Lean-core proof brings propext). -/
theorem le_of_add_le_add_left {a b c : Nat} (h : a + b ≤ a + c) : b ≤ c :=
  let step : (a + b) - a ≤ (a + c) - a := Nat.sub_le_sub_right h a
  -- (a+b) - a = b via add_comm + add_sub_cancel_right.
  let hb : (a + b) - a = b :=
    (congrArg (· - a) (Nat.add_comm a b)).trans (add_sub_cancel_right b a)
  let hc : (a + c) - a = c :=
    (congrArg (· - a) (Nat.add_comm a c)).trans (add_sub_cancel_right c a)
  -- Substitute LHS by RHS in step: b ≤ (a+c)-a, then b ≤ c.
  let step1 : b ≤ (a + c) - a :=
    Eq.subst (motive := fun x => x ≤ (a + c) - a) hb step
  Eq.subst (motive := fun x => b ≤ x) hc step1

/-- `a * (b - c) = a * b - a * c`.  ∅-axiom replacement for
    `Nat.mul_sub_left_distrib` (Lean-core proof brings propext).
    Term-mode pattern match on (b, c). -/
theorem mul_sub : ∀ (a b c : Nat), a * (b - c) = a * b - a * c
  | a, b, 0 =>
    -- a * (b - 0) = a * b = a * b - 0 = a * b - a * 0
    let h1 : a * 0 = 0 := Nat.mul_zero a
    let lhs : a * (b - 0) = a * b := rfl
    let rhs : a * b - a * 0 = a * b := h1 ▸ rfl
    lhs.trans rhs.symm
  | a, 0, c+1 =>
    -- a * (0 - (c+1)) = a * 0 = 0; a * 0 - a * (c+1) = 0 - a * (c+1) = 0
    let h0sub : (0:Nat) - (c+1) = 0 := Nat.zero_sub (c+1)
    let hmul0 : a * 0 = 0 := Nat.mul_zero a
    let hzs : (0:Nat) - a * (c+1) = 0 := Nat.zero_sub (a * (c+1))
    let lhs : a * (0 - (c+1)) = a * 0 := congrArg (a * ·) h0sub
    let rhs : a * 0 - a * (c+1) = 0 - a * (c+1) :=
      congrArg (· - a * (c+1)) hmul0
    -- a * (0 - (c+1)) = a * 0 = 0
    -- a * 0 - a * (c+1) = 0 - a * (c+1) = 0
    -- Both = 0, so equal.
    (lhs.trans hmul0).trans (hzs.symm.trans rhs.symm)
  | a, b+1, c+1 =>
    -- a * ((b+1) - (c+1)) = a * (b - c) [via Nat.succ_sub_succ_eq_sub]
    -- = a * b - a * c [by IH]
    -- = (a*b + a) - (a*c + a) [via add_sub_add_right.symm]
    -- = a*(b+1) - a*(c+1) [via Nat.mul_succ.symm]
    let s1 : (b+1) - (c+1) = b - c := Nat.succ_sub_succ_eq_sub b c
    let s2 : a * (b+1) = a * b + a := Nat.mul_succ a b
    let s3 : a * (c+1) = a * c + a := Nat.mul_succ a c
    let s4 : (a*b + a) - (a*c + a) = a*b - a*c := add_sub_add_right (a*b) a (a*c)
    let ih : a * (b - c) = a * b - a * c := mul_sub a b c
    let lhs : a * ((b+1) - (c+1)) = a * (b - c) := congrArg (a * ·) s1
    -- RHS: a * (b+1) - a * (c+1) = (a*b + a) - (a*c + a) = a*b - a*c
    let r1 : a * (b+1) - a * (c+1) = (a*b + a) - a * (c+1) :=
      congrArg (· - a * (c+1)) s2
    let r2 : (a*b + a) - a * (c+1) = (a*b + a) - (a*c + a) :=
      congrArg ((a*b + a) - ·) s3
    let rhs : a * (b+1) - a * (c+1) = a*b - a*c := (r1.trans r2).trans s4
    lhs.trans (ih.trans rhs.symm)

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

/-- `n < 6 → n ∈ {0,1,2,3,4,5}`.  ∅-axiom — used for CRT mod-6
    enumeration in `Lib.Math.ModArith.LensCRT.prod_refines_L6`. -/
theorem cases_lt_six {n : Nat} (h : n < 6) :
    n = 0 ∨ n = 1 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ n = 5 :=
  match Nat.lt_or_ge n 5 with
  | Or.inl hlt => (cases_lt_five hlt).imp id (·.imp id (·.imp id (·.imp id Or.inl)))
  | Or.inr hge =>
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (Nat.le_antisymm (Nat.le_of_lt_succ h) hge)))))

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

/-- Left mul cancellation: `0 < c ∧ c*a = c*b → a = b`.  ∅-axiom
    via antisymmetry of `≤` on `Nat.le_of_mul_le_mul_left`. -/
theorem mul_left_cancel_pos {c : Nat} (hc : 0 < c) {a b : Nat}
    (h : c * a = c * b) : a = b :=
  Nat.le_antisymm
    (Nat.le_of_mul_le_mul_left (Nat.le_of_eq h) hc)
    (Nat.le_of_mul_le_mul_left (Nat.le_of_eq h.symm) hc)

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

/-- ∅-axiom replacement for `Nat.sub_sub_self`: `m ≤ n → n - (n - m) = m`. -/
theorem sub_sub_self {n m : Nat} (h : m ≤ n) : n - (n - m) = m :=
  let h1 : n - m + m = n := sub_add_cancel h
  let h2 : m + (n - m) = n - m + m := Nat.add_comm m (n - m)
  let h3 : m + (n - m) = n := h2.trans h1
  Eq.subst (motive := fun x => x - (n - m) = m) h3
    (add_sub_cancel_right m (n - m))

/-- `a + 1 ≤ b → 1 ≤ b - a`.  ∅-axiom (term mode) — used in
    Cauchy seq files for "n - 1 ≥ 1 when n ≥ 2" patterns. -/
theorem le_pred_of_succ_le {a b : Nat} (h : a + 1 ≤ b) : 1 ≤ b - a :=
  let step : (a + 1) - a ≤ b - a := Nat.sub_le_sub_right h a
  let e1 : a + 1 = 1 + a := Nat.add_comm a 1
  let e2 : (1 + a) - a = 1 := add_sub_cancel_right 1 a
  let e3 : (a + 1) - a = 1 := e1 ▸ e2
  e3 ▸ step

/-- `1 ≤ a → (a + b) - 1 = (a - 1) + b`.  ∅-axiom (term mode) —
    used for sum-constraint preservation. -/
theorem add_sub_pred {a b : Nat} (ha : 1 ≤ a) :
    (a + b) - 1 = (a - 1) + b :=
  let e1 : a + b = b + a := Nat.add_comm a b
  let h1 : b + a - 1 = b + (a - 1) := add_sub_assoc b ha
  let e2 : b + (a - 1) = (a - 1) + b := Nat.add_comm b (a - 1)
  let r1 : a + b - 1 = b + a - 1 := e1 ▸ rfl
  r1.trans (h1.trans e2)

/-- `(0 : Nat) ≠ n + 1`.  ∅-axiom — for contradiction-closure
    patterns where standard `Nat.zero_ne_succ` would inflate axiom set. -/
theorem zero_ne_succ_213 (n : Nat) : (0 : Nat) ≠ n + 1 :=
  fun h => Nat.noConfusion h

/-- `(a * b) * (c * d) = (a * c) * (b * d)`.  ∅-axiom replacement for
    `Nat.mul_mul_mul_comm` (Lean-core proof brings propext).  Used in
    quadratic identity expansions (Pell invariant, Wallis recurrence). -/
theorem mul_mul_mul_comm_213 (a b c d : Nat) :
    (a * b) * (c * d) = (a * c) * (b * d) :=
  let h1 : (a * b) * (c * d) = a * (b * (c * d)) :=
    mul_assoc a b (c * d)
  let h2 : b * (c * d) = (b * c) * d := (mul_assoc b c d).symm
  let h3 : (b * c) * d = (c * b) * d := congrArg (· * d) (Nat.mul_comm b c)
  let h4 : (c * b) * d = c * (b * d) := mul_assoc c b d
  let middle : b * (c * d) = c * (b * d) := h2.trans (h3.trans h4)
  let h5 : a * (c * (b * d)) = (a * c) * (b * d) :=
    (mul_assoc a c (b * d)).symm
  h1.trans ((congrArg (a * ·) middle).trans h5)

end E213.Tactic.Nat213

namespace E213.Tactic.Nat213

/-- ∅-axiom replacement for `Nat.sub_le_sub_left` (Lean-core leaks
    `propext`).  Term-mode recursion on `c` + 4-case pattern on (a, b). -/
theorem sub_le_sub_left :
    ∀ (c : Nat) {a b : Nat}, a ≤ b → c - b ≤ c - a
  | 0, a, b, _ =>
      let h1 : (0 : Nat) - b = 0 := Nat.zero_sub b
      let h2 : (0 : Nat) - a = 0 := Nat.zero_sub a
      h1.symm ▸ h2.symm ▸ Nat.le_refl 0
  | _+1, 0, 0, _ => Nat.le_refl _
  | _+1, _+1, 0, h => absurd h (Nat.not_succ_le_zero _)
  | c+1, 0, b+1, _ =>
      let h_eq : c - b = (c+1) - (b+1) := (Nat.succ_sub_succ_eq_sub c b).symm
      let h_le : c - b ≤ c + 1 := Nat.le_trans (Nat.sub_le c b) (Nat.le_succ c)
      h_eq ▸ h_le
  | c+1, a+1, b+1, h =>
      let h' : a ≤ b := Nat.le_of_succ_le_succ h
      let ih : c - b ≤ c - a := sub_le_sub_left c h'
      let h_eq1 : c - b = (c+1) - (b+1) := (Nat.succ_sub_succ_eq_sub c b).symm
      let h_eq2 : c - a = (c+1) - (a+1) := (Nat.succ_sub_succ_eq_sub c a).symm
      Eq.subst (motive := fun x => x ≤ (c+1) - (a+1)) h_eq1
        (Eq.subst (motive := fun x => c - b ≤ x) h_eq2 ih)

/-- ∅-axiom replacement for `Nat.mod_mod` (Lean-core leaks `propext`).
    Direct case on `n`: `0 → rfl` via mod_zero, `n+1 → Nat.mod_eq_of_lt`. -/
theorem mod_mod_pure : ∀ (a n : Nat), a % n % n = a % n
  | a, 0 =>
      let h : a % 0 = a := Nat.mod_zero a
      h.symm ▸ h
  | a, n+1 => Nat.mod_eq_of_lt (Nat.mod_lt a (Nat.succ_pos n))

/-- `(a + n) % n = a % n` PURE (n ≥ 0 case included).  Building block
    for `add_mod_pure`.  Uses `Nat.mod_eq_sub_mod` + `add_sub_cancel_right`. -/
theorem add_self_mod_pure : ∀ (a n : Nat), (a + n) % n = a % n
  | a, 0 => rfl
  | a, n'+1 =>
      let hle : n'+1 ≤ a + (n'+1) := Nat.le_add_left _ _
      let h1 : (a + (n'+1)) % (n'+1) = (a + (n'+1) - (n'+1)) % (n'+1) :=
        Nat.mod_eq_sub_mod hle
      let h2 : a + (n'+1) - (n'+1) = a := add_sub_cancel_right a (n'+1)
      h1.trans (congrArg (· % (n'+1)) h2)

end E213.Tactic.Nat213

namespace E213.Tactic.Nat213

/-- `0 % m = 0`.  ∅-axiom replacement for Lean-core `Nat.zero_mod`
    (which is `[propext]`).  Term-mode pattern match on `m`.

    Companion to `E213.Meta.Nat.AddMod213.zero_mod`
    (Lib/Math layer); this Term-layer version is the bedrock. -/
theorem zero_mod (m : Nat) : 0 % m = 0 :=
  match m with
  | 0 => rfl
  | _+1 => rfl

/-- `m * b % m = 0`.  ∅-axiom replacement for Lean-core
    `Nat.mul_mod_right` (which uses `Nat.zero_mod` + `Nat.add_mod_right`,
    both `[propext]`).  Term-mode recursion on `b` using PURE
    `Nat.mod_eq_sub_mod` and `add_sub_cancel_right`.  No tactics
    used (Term layer requires literally 0-axiom — no propext-tainted
    `rw` infrastructure). -/
theorem mul_mod_right (m : Nat) : ∀ b, m * b % m = 0
  | 0 =>
    let h1 : m * 0 = 0 := Nat.mul_zero m
    h1.symm ▸ zero_mod m
  | b+1 =>
    let ih : m * b % m = 0 := mul_mod_right m b
    let hsucc : m * (b + 1) = m * b + m := Nat.mul_succ m b
    let hge : m ≤ m * b + m := Nat.le_add_left m (m * b)
    let hms : (m * b + m) % m = (m * b + m - m) % m :=
      Nat.mod_eq_sub_mod hge
    let hcancel : m * b + m - m = m * b := add_sub_cancel_right (m * b) m
    let step1 : m * (b + 1) % m = (m * b + m) % m :=
      congrArg (· % m) hsucc
    let step3 : (m * b + m - m) % m = m * b % m :=
      congrArg (· % m) hcancel
    (step1.trans (hms.trans step3)).trans ih

end E213.Tactic.Nat213

namespace E213.Tactic.Nat213

/-- `a ≤ Nat.max a b`.  ∅-axiom replacement for Lean-core
    `Nat.le_max_left` (`[propext]`).  Term-mode via `Decidable.casesOn`
    on `Nat.decLe`.  No tactics — strict Term-layer purity. -/
theorem le_max_left (a b : Nat) : a ≤ Nat.max a b :=
  show a ≤ if a ≤ b then b else a from
    (Nat.decLe a b).casesOn
      (fun h => (if_neg h).symm ▸ Nat.le_refl a)
      (fun h => (if_pos h).symm ▸ h)

/-- `b ≤ Nat.max a b`.  ∅-axiom replacement for Lean-core
    `Nat.le_max_right` (`[propext]`).  Term-mode. -/
theorem le_max_right (a b : Nat) : b ≤ Nat.max a b :=
  show b ≤ if a ≤ b then b else a from
    (Nat.decLe a b).casesOn
      (fun h => (if_neg h).symm ▸ Nat.le_of_lt (Nat.lt_of_not_le h))
      (fun h => (if_pos h).symm ▸ Nat.le_refl b)

end E213.Tactic.Nat213

namespace E213.Tactic.Nat213

/-- `2 * n = n + n`.  Term-mode by structural recursion.

    Companion to Lean-core `Nat.two_mul` (also ∅-axiom);
    provided here so 213 code can stay within `E213.Tactic.Nat213`
    vocabulary without leaning on Lean-core Nat lemmas.

    Term-mode only (no `rw`) for Term-layer purity. -/
theorem two_mul : ∀ (n : Nat), 2 * n = n + n
  | 0 => rfl
  | n+1 =>
    let ih : 2 * n = n + n := two_mul n
    let h1 : 2 * (n + 1) = 2 * n + 2 := Nat.mul_succ 2 n
    let h2 : 2 * n + 2 = n + n + 2 := congrArg (· + 2) ih
    -- `(n+1) + (n+1) = ((n+1) + n) + 1 = ((n+n) + 1) + 1 = n + n + 2`.
    -- Each step is either rfl (by Nat.add's definition) or
    -- `Nat.succ_add n n : (n+1) + n = (n+n) + 1`.
    let h3 : (n + 1) + n = n + n + 1 := Nat.succ_add n n
    let h4 : (n + 1) + (n + 1) = ((n + 1) + n) + 1 := rfl
    let h5 : ((n + 1) + n) + 1 = (n + n + 1) + 1 := congrArg (· + 1) h3
    let h6 : (n + n + 1) + 1 = n + n + 2 := rfl
    h1.trans (h2.trans (h4.trans (h5.trans h6)).symm)

/-! ### `gcd213` — 213-native gcd (∅-axiom)

    Lean-core `Nat.gcd` uses well-founded recursion whose termination
    proof brings `propext` into any `#print axioms` of theorems that
    mention `Nat.gcd 〈literal〉 〈literal〉`.  This 213-native variant
    uses fuel-driven structural recursion: closed terms reduce by
    `rfl` and stay ∅-axiom.

    `gcdFuel n a b` runs the Euclidean step at most `n` times.
    `gcd213 a b` allocates `2 * (a + b) + 1` fuel — sufficient for
    any Euclidean descent on `(a, b)` (the bound `M(a, b) :=
    Nat.max a b + a` strictly decreases each step; `2*(a+b) ≥ M`). -/

/-- Fuel-driven Euclidean recursion (structural on fuel). -/
def gcdFuel : Nat → Nat → Nat → Nat
  | 0,    a,    _ => a
  | _+1,  0,    b => b
  | n+1,  a+1,  b => gcdFuel n (b % (a+1)) (a+1)

/-- 213-native gcd.  `rfl` reduces closed terms; ∅-axiom. -/
def gcd213 (a b : Nat) : Nat := gcdFuel (2 * (a + b) + 1) a b

end E213.Tactic.Nat213
