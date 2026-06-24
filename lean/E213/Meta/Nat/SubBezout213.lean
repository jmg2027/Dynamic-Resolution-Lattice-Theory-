import E213.Meta.Nat.SubGcd213

/-!
# Structural Bézout (extended Euclid on `subDiv`/`subMod`) — the FTA-uniqueness key (∅-axiom)

The remaining wall after `SubGcd213` (gcd + prime-coprimality without Bézout): **Euclid's lemma**'s
*other* half — `gcd(p,a)=1 → p ∣ a·b → p ∣ b` — needs a **Bézout witness**, and the repo has none in
grounded form (`ModArith.ModBezout` only `decide`s smoke tests and uses `Nat.div`/`Nat.mod`).

This file builds it structurally.  The extended Euclidean recursion threads a coefficient quadruple
`(g, x, y, s)` (`s : Bool` a sign flag), with the **Nat-only** Bézout invariant

  `s = true  → a·x = b·y + g`   (combination on the `+a` side)
  `s = false → b·y = a·x + g`   (combination on the `+b` side)

so no signed integers / `Int` are needed.  The Euclidean step `a = b·q + r` (`subDivMod_eq`, no Nat
subtraction in the algebra) gives the uniform update `xₙ = y'`, `yₙ = x' + q·y'`, `s` flips —
verified by distribution + the IH.

  * `egcd` — the extended recursion (structural `Nat.rec` on fuel);
  * `egcd_fst` — its `g`-component equals `gcdSub` (so `= gcd`);
  * `egcd_bezout` — the sign-cased Bézout invariant;
  * `bezout_one_of_coprime` — `gcd(a,b)=1` ⇒ `∃ x y, a·x = b·y+1 ∨ b·y = a·x+1` (one-sided Nat form).

∅-axiom; `subMod`/`subDiv`-based — no `Nat.div`, no `Nat.mod`, no `Nat.lt_wfRel`.
-/

namespace E213.Meta.Nat.SubBezout213

open E213.Meta.Nat.SubMod213 (subMod subDiv subMod_lt subDivMod_eq)
open E213.Meta.Nat.SubGcd213 (gcdSub gcdW gcdW_dvd_left gcdW_dvd_right)

/-- Extended Euclidean recursion: `egcd fuel a b = (g, x, y, s)` with `g = gcd(a,b)` and the sign-cased
    Bézout invariant (`egcd_bezout`).  Structural `Nat.rec` on fuel; mirrors `gcdSub`'s recursion with
    coefficient threading.  The update `(x,y,s) ↦ (y', x'+q·y', !s')` is forced by `a = b·q + r`. -/
def egcd : Nat → Nat → Nat → (Nat × Nat × Nat × Bool)
  | 0,     a, _ => (a, 1, 0, true)
  | f + 1, a, b =>
    match b with
    | 0     => (a, 1, 0, true)
    | b'+1  =>
      let q := subDiv a a (b'+1)
      let r := subMod a a (b'+1)
      let t := egcd f (b'+1) r
      (t.1, t.2.2.1, t.2.1 + q * t.2.2.1, !t.2.2.2)

/-- The `g`-component of `egcd` is exactly `gcdSub` — same recursion, coefficients stripped. -/
theorem egcd_fst : ∀ (fuel a b : Nat), (egcd fuel a b).1 = gcdSub fuel a b
  | 0,     _, _ => rfl
  | f + 1, a, b => by
    match b with
    | 0      => rfl
    | b' + 1 =>
      show (egcd f (b' + 1) (subMod a a (b' + 1))).1
            = gcdSub f (b' + 1) (subMod a a (b' + 1))
      exact egcd_fst f (b' + 1) (subMod a a (b' + 1))

/-- ★★★ **The Bézout invariant.**  With ample fuel (`b ≤ fuel`), the coefficient quadruple
    `(g, x, y, s) = egcd fuel a b` satisfies the sign-cased Nat identity: `s = true → a·x = b·y + g`
    and `s = false → b·y = a·x + g`.  By `Nat.rec` on fuel; the step substitutes `a = b·q + r`
    (`subDivMod_eq`) into the IH and the sign flips.  No Nat subtraction in the algebra. -/
theorem egcd_bezout : ∀ (fuel a b : Nat), b ≤ fuel →
    ((egcd fuel a b).2.2.2 = true →
        a * (egcd fuel a b).2.1 = b * (egcd fuel a b).2.2.1 + (egcd fuel a b).1) ∧
    ((egcd fuel a b).2.2.2 = false →
        b * (egcd fuel a b).2.2.1 = a * (egcd fuel a b).2.1 + (egcd fuel a b).1)
  | 0,     a, b, hb => by
    have hb0 : b = 0 := Nat.le_antisymm hb (Nat.zero_le b)
    subst hb0
    refine ⟨fun _ => ?_, fun h => Bool.noConfusion h⟩
    show a * 1 = 0 * 0 + a
    rw [Nat.mul_one, Nat.mul_zero, Nat.zero_add]
  | f + 1, a, b, hb => by
    match b, hb with
    | 0,      _  =>
      refine ⟨fun _ => ?_, fun h => Bool.noConfusion h⟩
      show a * 1 = 0 * 0 + a
      rw [Nat.mul_one, Nat.mul_zero, Nat.zero_add]
    | b' + 1, hb =>
      have hr_lt : subMod a a (b' + 1) < b' + 1 :=
        subMod_lt a a (b' + 1) (Nat.zero_lt_succ b') (Nat.le_refl a)
      have hr_le_f : subMod a a (b' + 1) ≤ f :=
        Nat.le_of_lt_succ (Nat.lt_of_lt_of_le hr_lt hb)
      obtain ⟨ih_t, ih_f⟩ := egcd_bezout f (b' + 1) (subMod a a (b' + 1)) hr_le_f
      have ha : (b' + 1) * subDiv a a (b' + 1) + subMod a a (b' + 1) = a :=
        subDivMod_eq a a (b' + 1)
      show (((!(egcd f (b' + 1) (subMod a a (b' + 1))).2.2.2) = true) →
              a * (egcd f (b' + 1) (subMod a a (b' + 1))).2.2.1
                = (b' + 1) * ((egcd f (b' + 1) (subMod a a (b' + 1))).2.1
                    + subDiv a a (b' + 1) * (egcd f (b' + 1) (subMod a a (b' + 1))).2.2.1)
                  + (egcd f (b' + 1) (subMod a a (b' + 1))).1)
            ∧ (((!(egcd f (b' + 1) (subMod a a (b' + 1))).2.2.2) = false) →
              (b' + 1) * ((egcd f (b' + 1) (subMod a a (b' + 1))).2.1
                  + subDiv a a (b' + 1) * (egcd f (b' + 1) (subMod a a (b' + 1))).2.2.1)
                = a * (egcd f (b' + 1) (subMod a a (b' + 1))).2.2.1
                  + (egcd f (b' + 1) (subMod a a (b' + 1))).1)
      generalize hq : subDiv a a (b' + 1) = q at ha ⊢
      generalize hr : subMod a a (b' + 1) = r at ha ih_t ih_f ⊢
      generalize ht : egcd f (b' + 1) r = t at ih_t ih_f ⊢
      obtain ⟨g, x', y', s'⟩ := t
      -- ha : (b'+1)*q + r = a ;  ih_t : s'=true → (b'+1)*x' = r*y'+g ;  ih_f : s'=false → r*y' = (b'+1)*x'+g
      -- key distributions
      have hA : a * y' = (b' + 1) * (q * y') + r * y' := by
        rw [← ha, E213.Tactic.NatHelper.add_mul, E213.Tactic.NatHelper.mul_assoc]
      have hB : (b' + 1) * (x' + q * y') = (b' + 1) * x' + (b' + 1) * (q * y') := by
        rw [Nat.mul_add]
      cases s' with
      | false =>
        refine ⟨fun _ => ?_, fun h => Bool.noConfusion h⟩
        show a * y' = (b' + 1) * (x' + q * y') + g
        have hif : r * y' = (b' + 1) * x' + g := ih_f rfl
        rw [hA, hB, hif, ← Nat.add_assoc,
            Nat.add_comm ((b' + 1) * (q * y')) ((b' + 1) * x')]
      | true =>
        refine ⟨fun h => Bool.noConfusion h, fun _ => ?_⟩
        show (b' + 1) * (x' + q * y') = a * y' + g
        have hit : (b' + 1) * x' = r * y' + g := ih_t rfl
        rw [hB, hit, hA, Nat.add_right_comm, Nat.add_comm (r * y') ((b' + 1) * (q * y'))]

/-- ★★★ **One-sided Nat Bézout from coprimality.**  When `gcd(a,b) = 1` (`gcdW`), there are Nat
    coefficients `x, y` with `a·x = b·y + 1` *or* `b·y = a·x + 1` — the sign-cased Bézout identity
    read off `egcd`.  This is the witness Euclid's lemma needs; no `Int`, no signed integers.  The
    `egcd` `g`-component equals `gcdW a b = 1` via `egcd_fst`. -/
theorem bezout_one_of_coprime {a b : Nat} (h : gcdW a b = 1) :
    ∃ x y, a * x = b * y + 1 ∨ b * y = a * x + 1 := by
  have hb_le : b ≤ a + b := Nat.le_add_left b a
  have hg : (egcd (a + b) a b).1 = 1 := by rw [egcd_fst]; exact h
  obtain ⟨bt, bf⟩ := egcd_bezout (a + b) a b hb_le
  refine ⟨(egcd (a + b) a b).2.1, (egcd (a + b) a b).2.2.1, ?_⟩
  cases hs : (egcd (a + b) a b).2.2.2 with
  | true  => exact Or.inl (by have := bt hs; rwa [hg] at this)
  | false => exact Or.inr (by have := bf hs; rwa [hg] at this)

end E213.Meta.Nat.SubBezout213
