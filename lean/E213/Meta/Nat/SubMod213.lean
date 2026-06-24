import E213.Meta.Tactic.NatHelper

/-!
# Structural division/remainder by repeated subtraction — `lt_wfRel`-free (∅-axiom)

The descent leg's residual after grounding the FTA *descent* in `isPart_wf` (`MulDescentGrounded`) is
`Nat.lt_wfRel`, isolated to core `Nat.div`/`Nat.mod` (kernel well-founded-recursion).  This file
rebuilds the remainder **structurally** — repeated `Nat.sub` over a fuel parameter (`Nat.rec`) — so
the divisibility test it powers carries **no** `Nat.lt_wfRel` and **no** `Nat.mod`.  `Nat.sub` is
itself structural and clean (verified `lt_wfRel`-free), so this is division rebuilt from the repo's
own subtraction, per the descent-leg programme (`research-notes/frontiers/the_descent_leg.md`).

  * `subMod fuel a b` — `a` reduced mod `b` by subtracting `b` while `a ≥ b`;
  * `subMod_eq` — the quotient/remainder identity `a = b * q + subMod fuel a b` (`Nat.rec` on fuel);
  * `subMod_lt` — `subMod fuel a b < b` once `a ≤ fuel` and `0 < b`;
  * `subMod_zero_iff_dvd` — `subMod a a b = 0 ↔ b ∣ a` (both directions), the `Nat.mod`-free
    replacement for `n % b = 0 ↔ b ∣ n`.

∅-axiom; closure is `Nat.sub` / `Nat.rec` only — no `Nat.div`, no `Nat.mod`, no `Nat.lt_wfRel`.
-/

namespace E213.Meta.Nat.SubMod213

/-- `a mod b` by repeated subtraction, bounded by `fuel`.  Structural recursion on `fuel`. -/
def subMod : Nat → Nat → Nat → Nat
  | 0,     a, _ => a
  | f + 1, a, b => if a < b then a else subMod f (a - b) b

/-- The quotient/remainder identity: `a = b * q + subMod fuel a b` for some `q`.  Pure `Nat.rec` on
    `fuel`. -/
theorem subMod_eq : ∀ (fuel a b : Nat), ∃ q, a = b * q + subMod fuel a b
  | 0,     a, b => ⟨0, by show a = b * 0 + a; rw [Nat.mul_zero, Nat.zero_add]⟩
  | f + 1, a, b => by
    show ∃ q, a = b * q + (if a < b then a else subMod f (a - b) b)
    by_cases h : a < b
    · exact ⟨0, by rw [if_pos h, Nat.mul_zero, Nat.zero_add]⟩
    · have hba : b ≤ a := Nat.le_of_not_lt h
      obtain ⟨q', hq'⟩ := subMod_eq f (a - b) b
      rw [if_neg h]
      refine ⟨q' + 1, ?_⟩
      calc a = b + (a - b) :=
            ((Nat.add_comm b (a - b)).trans (E213.Tactic.NatHelper.sub_add_cancel hba)).symm
        _ = b + (b * q' + subMod f (a - b) b) := congrArg (fun z => b + z) hq'
        _ = (b + b * q') + subMod f (a - b) b := (Nat.add_assoc b (b * q') _).symm
        _ = (b * q' + b) + subMod f (a - b) b := by rw [Nat.add_comm b (b * q')]
        _ = b * (q' + 1) + subMod f (a - b) b := by rw [Nat.mul_succ]

/-- The remainder is below the divisor once the fuel is ample (`a ≤ fuel`) and `0 < b`. -/
theorem subMod_lt : ∀ (fuel a b : Nat), 0 < b → a ≤ fuel → subMod fuel a b < b
  | 0,     a, b, hb, hle => by
    have ha0 : a = 0 := Nat.le_antisymm hle (Nat.zero_le a)
    show subMod 0 a b < b
    rw [ha0]; exact hb
  | f + 1, a, b, hb, hle => by
    show (if a < b then a else subMod f (a - b) b) < b
    by_cases h : a < b
    · rw [if_pos h]; exact h
    · rw [if_neg h]
      have hba : b ≤ a := Nat.le_of_not_lt h
      have hsub_lt : a - b < a := Nat.sub_lt (Nat.lt_of_lt_of_le hb hba) hb
      exact subMod_lt f (a - b) b hb (Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hsub_lt hle))

/-- Left-cancellation of `≤` over `+`, propext-free (core `Nat.le_of_add_le_add_left` leaks propext).
    By `Nat.rec` on the cancelled summand. -/
private theorem le_add_cancel_left : ∀ (a : Nat) {b c : Nat}, a + b ≤ a + c → b ≤ c
  | 0,     b, c, h => by rw [Nat.zero_add, Nat.zero_add] at h; exact h
  | a + 1, b, c, h => by
      apply le_add_cancel_left a
      apply Nat.le_of_succ_le_succ
      rw [← Nat.succ_add, ← Nat.succ_add]
      exact h

/-- ★★★ **Divisibility decision, `Nat.mod`-free.**  `subMod a a b = 0 ↔ b ∣ a` (for `0 < b`).  The
    structural, `lt_wfRel`-free replacement for `n % b = 0 ↔ b ∣ n` — forward from `subMod_eq`
    (`a = b*q + 0`), backward from `subMod_eq` + `subMod_lt` (`b ∣ a` and remainder `< b` force `0`). -/
theorem subMod_zero_iff_dvd (a b : Nat) (hb : 0 < b) :
    subMod a a b = 0 ↔ b ∣ a := by
  obtain ⟨q, hq⟩ := subMod_eq a a b
  constructor
  · intro h0
    refine ⟨q, ?_⟩
    rw [h0, Nat.add_zero] at hq
    exact hq
  · intro hdvd
    obtain ⟨c, hc⟩ := hdvd
    have hlt : subMod a a b < b := subMod_lt a a b hb (Nat.le_refl a)
    -- b * q + r = b * c   (r := subMod a a b)
    have hbq : b * q + subMod a a b = b * c := by rw [← hq]; exact hc
    rcases Nat.lt_or_ge q c with hqc | hqc
    · -- q < c ⟹ b*q + b ≤ b*c = b*q + r ⟹ b ≤ r, contra r < b
      exfalso
      have hstep : b * q + b ≤ b * c := by
        have h1 : b * (q + 1) ≤ b * c := Nat.mul_le_mul (Nat.le_refl b) hqc
        rw [Nat.mul_succ] at h1; exact h1
      have hbr : b ≤ subMod a a b := by
        apply le_add_cancel_left (b * q)
        show b * q + b ≤ b * q + subMod a a b
        rw [hbq]; exact hstep
      exact Nat.lt_irrefl b (Nat.lt_of_le_of_lt hbr hlt)
    · -- q ≥ c ⟹ b*c ≤ b*q, and b*q + r = b*c ⟹ r = 0
      have hbc_le : b * c ≤ b * q := Nat.mul_le_mul (Nat.le_refl b) hqc
      have hr0 : subMod a a b ≤ 0 := by
        apply le_add_cancel_left (b * q)
        show b * q + subMod a a b ≤ b * q + 0
        rw [Nat.add_zero, hbq]; exact hbc_le
      exact Nat.le_antisymm hr0 (Nat.zero_le _)

end E213.Meta.Nat.SubMod213
