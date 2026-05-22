/-!
# Bool-OR ladder existence iff template — G107 §3 REAL-1+REAL-2

The recurring bool-OR-ladder pattern:

    ladder 0     = P 0
    ladder (n+1) = P (n+1) || ladder n

appears in `cutSumAux`, `cutMulInner`, `cutMulOuter`, and similar
bounded-search definitions.  The associated existence iff

    ladder n = true ↔ ∃ i ≤ n, P i = true

was previously hand-rolled per call site (~50-70 lines each, 4+ sites
in Real213).  This template extracts the inductive proof once.

Lives in `Real213/Sum/` so it's upstream of FluxMVT and downstream of
core Nat/Bool.  Companion to `Mul/CutMulOuterReduce.lean` (G110 FLUX-1
upstream template, which extracts a different pattern).

PURE — verified standalone (no propext, no Quot.sound).  Connecting to
`match`-defined ladders works via `rfl` for the per-arm equations.
Uses `iff.mp/mpr` directly (no `rw [iff]`) at the call sites to keep
∅-axiom.
-/

namespace E213.Lib.Math.Real213.Sum.BoolOrLadder

/-- ★ Generic bool-OR ladder existence iff.  PURE. -/
theorem bool_or_ladder_iff
    (P : Nat → Bool) (ladder : Nat → Bool)
    (h_zero : ladder 0 = P 0)
    (h_succ : ∀ n, ladder (n+1) = (P (n+1) || ladder n)) :
    ∀ n, ladder n = true ↔ ∃ i, i ≤ n ∧ P i = true := by
  intro n
  induction n with
  | zero =>
    constructor
    · intro h
      exact ⟨0, Nat.le_refl _, by rw [← h_zero]; exact h⟩
    · rintro ⟨i, hi, hP⟩
      have hi0 : i = 0 := Nat.le_zero.mp hi
      subst hi0; rw [h_zero]; exact hP
  | succ j ih =>
    constructor
    · intro h
      rw [h_succ] at h
      cases hP : P (j+1) with
      | true => exact ⟨j+1, Nat.le_refl _, hP⟩
      | false =>
        rw [hP] at h
        obtain ⟨i, hi, hP'⟩ := ih.mp h
        exact ⟨i, Nat.le_succ_of_le hi, hP'⟩
    · rintro ⟨i, hi, hP⟩
      rw [h_succ]
      rcases Nat.lt_or_ge i (j+1) with h_lt | h_ge
      · have hi' : i ≤ j := Nat.lt_succ_iff.mp h_lt
        have rec_true : ladder j = true := ih.mpr ⟨i, hi', hP⟩
        rw [rec_true]; cases P (j+1) <;> rfl
      · have h_eq : i = j+1 := Nat.le_antisymm hi h_ge
        subst h_eq; rw [hP]; rfl

/-- ★ PURE bool AND extension iff.  Lean core's `Bool.and_eq_true`
    depends on `propext`; this proof avoids it. -/
theorem and_eq_true_pure (a b : Bool) : (a && b) = true ↔ a = true ∧ b = true := by
  constructor
  · intro h
    cases ha : a with
    | true =>
      cases hb : b with
      | true => exact ⟨rfl, rfl⟩
      | false => rw [ha, hb] at h; cases h
    | false => rw [ha] at h; cases h
  · rintro ⟨ha, hb⟩; rw [ha, hb]; rfl

/-- ★ PURE bool AND-AND extension (3-conjunct, for `cutMulInner`). -/
theorem and3_eq_true_pure (a b c : Bool) :
    (a && b && c) = true ↔ a = true ∧ b = true ∧ c = true := by
  constructor
  · intro h
    have h1 := (and_eq_true_pure (a && b) c).mp h
    have h2 := (and_eq_true_pure a b).mp h1.1
    exact ⟨h2.1, h2.2, h1.2⟩
  · rintro ⟨ha, hb, hc⟩
    exact (and_eq_true_pure (a && b) c).mpr
      ⟨(and_eq_true_pure a b).mpr ⟨ha, hb⟩, hc⟩

end E213.Lib.Math.Real213.Sum.BoolOrLadder
